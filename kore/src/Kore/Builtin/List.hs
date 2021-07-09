{- |
Module      : Kore.Builtin.List
Description : Built-in associative lists
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.List as List
@
-}
module Kore.Builtin.List (
    sort,
    assertSort,
    verifiers,
    builtinFunctions,
    returnList,
    asPattern,
    asInternal,
    internalize,

    -- * Symbols
    lookupSymbolGet,
    isSymbolConcat,
    isSymbolElement,
    isSymbolUnit,
    unifyEquals,

    -- * keys
    concatKey,
    elementKey,
    unitKey,
    getKey,

    -- * Evaluators
    evalConcat,
    evalElement,
    evalUnit,
    expectConcreteBuiltinList,
) where

import Control.Error (
    MaybeT,
    hoistMaybe,
 )
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans.Maybe as Monad.Trans.Maybe (
    mapMaybeT,
 )
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import qualified Data.Reflection as Reflection
import Data.Sequence (
    Seq,
 )
import qualified Data.Sequence as Seq
import Data.Text (
    Text,
 )
import qualified Kore.Builtin.Bool as Bool
import Kore.Builtin.Builtin (
    acceptAnySort,
 )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import Kore.Builtin.List.List
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.Internal.InternalList
import Kore.Internal.Pattern (
    Conditional (..),
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike (
    Key,
    Sort,
    TermLike,
    mkApplySymbol,
    mkInternalList,
    mkSort,
    retractKey,
    termLikeSort,
    pattern App_,
    pattern ElemVar_,
    pattern InternalList_,
    pattern Var_,
 )
import qualified Kore.Internal.TermLike as TermLike (
    Symbol (..),
    isFunctionPattern,
    markSimplified,
 )
import Kore.Log.DebugUnifyBottom (
    debugUnifyBottom,
 )
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Syntax.Sentence (
    SentenceSort (..),
 )
import Kore.Unification.Unify (
    MonadUnify,
 )
import Prelude.Kore

{- | Verify that the sort is hooked to the builtin @List@ sort.

  See also: 'sort', 'Builtin.verifySort'
-}
assertSort :: Builtin.SortVerifier
assertSort = Builtin.verifySort sort

{- | Is the given sort hooked to the builtin List sort?

Returns Nothing if the sort is unknown (i.e. the _PREDICATE sort).
Returns Just False if the sort is a variable.
-}
isListSort :: SmtMetadataTools attrs -> Sort -> Maybe Bool
isListSort = Builtin.isSort sort

verifiers :: Builtin.Verifiers
verifiers =
    Builtin.Verifiers
        { sortDeclVerifiers
        , symbolVerifiers
        , patternVerifierHook = mempty
        }

{- | Verify that hooked sort declarations are well-formed.

  See also: 'Builtin.verifySortDecl'
-}
sortDeclVerifiers :: Builtin.SortDeclVerifiers
sortDeclVerifiers =
    HashMap.fromList [(sort, verifySortDecl)]
  where
    verifySortDecl indexedModule sentenceSort attrs = do
        Builtin.verifySortDecl indexedModule sentenceSort attrs
        unitId <- Builtin.getUnitId attrs
        Builtin.assertSymbolHook indexedModule unitId unitKey
        Builtin.assertSymbolResultSort indexedModule unitId expectedSort
        elementId <- Builtin.getElementId attrs
        Builtin.assertSymbolHook indexedModule elementId elementKey
        Builtin.assertSymbolResultSort indexedModule elementId expectedSort
        concatId <- Builtin.getConcatId attrs
        Builtin.assertSymbolHook indexedModule concatId concatKey
        Builtin.assertSymbolResultSort indexedModule concatId expectedSort
        return ()
      where
        SentenceSort{sentenceSortName} = sentenceSort
        expectedSort = mkSort sentenceSortName

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'
-}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
        [
            ( concatKey
            , Builtin.verifySymbol assertSort [assertSort, assertSort]
            )
        ,
            ( elementKey
            , Builtin.verifySymbol assertSort [acceptAnySort]
            )
        ,
            ( unitKey
            , Builtin.verifySymbol assertSort []
            )
        ,
            ( getKey
            , Builtin.verifySymbol acceptAnySort [assertSort, Int.assertSort]
            )
        ,
            ( updateKey
            , Builtin.verifySymbol
                assertSort
                [assertSort, Int.assertSort, acceptAnySort]
            )
        ,
            ( inKey
            , Builtin.verifySymbol Bool.assertSort [acceptAnySort, assertSort]
            )
        ,
            ( sizeKey
            , Builtin.verifySymbol Int.assertSort [assertSort]
            )
        ,
            ( makeKey
            , Builtin.verifySymbol assertSort [Int.assertSort, acceptAnySort]
            )
        ,
            ( updateAllKey
            , Builtin.verifySymbol assertSort [assertSort, Int.assertSort, assertSort]
            )
        ]

{- | Abort function evaluation if the argument is not a List domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainList', it is a bug.
-}
expectBuiltinList ::
    Monad m =>
    -- | Context for error message
    Text ->
    -- | Operand pattern
    TermLike variable ->
    MaybeT m (Seq (TermLike variable))
expectBuiltinList _ =
    \case
        InternalList_ InternalList{internalListChild} ->
            return internalListChild
        _ -> empty

expectConcreteBuiltinList ::
    Monad m =>
    -- | Context for error message
    Text ->
    -- | Operand pattern
    TermLike variable ->
    MaybeT m (Seq Key)
expectConcreteBuiltinList ctx =
    Monad.Trans.Maybe.mapMaybeT (fmap Monad.join)
        . fmap (traverse retractKey)
        . expectBuiltinList ctx

returnList ::
    (MonadSimplify m, InternalVariable variable) =>
    Sort ->
    Seq (TermLike variable) ->
    m (Pattern variable)
returnList builtinListSort builtinListChild = do
    tools <- Simplifier.askMetadataTools
    return (Reflection.give tools $ asPattern builtinListSort builtinListChild)

evalElement :: Builtin.Function
evalElement _ resultSort =
    \case
        [elem'] -> returnList resultSort (Seq.singleton elem')
        _ -> Builtin.wrongArity elementKey

evalGet :: Builtin.Function
evalGet _ resultSort [_list, _ix] = do
    let emptyList = do
            _list <- expectBuiltinList getKey _list
            if Seq.null _list
                then return (Pattern.bottomOf resultSort)
                else empty
        bothConcrete = do
            _list <- expectBuiltinList getKey _list
            _ix <- fromInteger <$> Int.expectBuiltinInt getKey _ix
            let ix
                    | _ix < 0 =
                        -- negative indices count from end of list
                        _ix + Seq.length _list
                    | otherwise = _ix
            return (maybeBottom (Seq.lookup ix _list))
    emptyList <|> bothConcrete
  where
    maybeBottom =
        maybe Pattern.bottom Pattern.fromTermLike
evalGet _ _ _ = Builtin.wrongArity getKey

evalUpdate :: Builtin.Function
evalUpdate _ resultSort [_list, _ix, value] = do
    _list <- expectBuiltinList getKey _list
    _ix <- fromInteger <$> Int.expectBuiltinInt getKey _ix
    let len = Seq.length _list
    if _ix >= 0 && _ix < len
        then returnList resultSort (Seq.update _ix value _list)
        else return (Pattern.bottomOf resultSort)
evalUpdate _ _ _ = Builtin.wrongArity updateKey

evalIn :: Builtin.Function
evalIn _ resultSort [_elem, _list] = do
    _list <- expectConcreteBuiltinList inKey _list
    _elem <- hoistMaybe $ retractKey _elem
    _elem `elem` _list
        & Bool.asPattern resultSort
        & return
evalIn _ _ _ = Builtin.wrongArity inKey

evalUnit :: Builtin.Function
evalUnit _ resultSort =
    \case
        [] -> returnList resultSort Seq.empty
        _ -> Builtin.wrongArity "LIST.unit"

evalConcat :: Builtin.Function
evalConcat _ resultSort [_list1, _list2] = do
    let leftIdentity = do
            _list1 <- expectBuiltinList concatKey _list1
            if Seq.null _list1
                then return (Pattern.fromTermLike _list2)
                else empty
        rightIdentity = do
            _list2 <- expectBuiltinList concatKey _list2
            if Seq.null _list2
                then return (Pattern.fromTermLike _list1)
                else empty
        bothConcrete = do
            _list1 <- expectBuiltinList concatKey _list1
            _list2 <- expectBuiltinList concatKey _list2
            returnList resultSort (_list1 <> _list2)
    leftIdentity <|> rightIdentity <|> bothConcrete
evalConcat _ _ _ = Builtin.wrongArity concatKey

evalSize :: Builtin.Function
evalSize _ resultSort [_list] = do
    _list <- expectBuiltinList sizeKey _list
    Seq.length _list
        & fromIntegral
        & Int.asPattern resultSort
        & return
evalSize _ _ _ = Builtin.wrongArity sizeKey

evalMake :: Builtin.Function
evalMake _ resultSort [_len, value] = do
    _len <- fromInteger <$> Int.expectBuiltinInt getKey _len
    if _len >= 0
        then returnList resultSort (Seq.replicate _len value)
        else return (Pattern.bottomOf resultSort)
evalMake _ _ _ = Builtin.wrongArity sizeKey

evalUpdateAll :: Builtin.Function
evalUpdateAll _ resultSort [_list1, _ix, _list2] = do
    _list1 <- expectBuiltinList getKey _list1
    _list2 <- expectBuiltinList getKey _list2
    _ix <- fromInteger <$> Int.expectBuiltinInt getKey _ix
    let len1 = Seq.length _list1
        len2 = Seq.length _list2
        result
            | _ix < 0 = return (Pattern.bottomOf resultSort)
            | len2 == 0 = returnList resultSort _list1
            | _ix + len2 > len1 = return (Pattern.bottomOf resultSort)
            | otherwise =
                let unchanged1 = Seq.take _ix _list1
                    unchanged2 = Seq.drop (_ix + length _list2) _list1
                 in returnList resultSort (unchanged1 <> _list2 <> unchanged2)
    result
evalUpdateAll _ _ _ = Builtin.wrongArity updateKey

-- | Implement builtin function evaluation.
builtinFunctions :: Map Text BuiltinAndAxiomSimplifier
builtinFunctions =
    Map.fromList
        [ (concatKey, Builtin.functionEvaluator evalConcat)
        , (elementKey, Builtin.functionEvaluator evalElement)
        , (unitKey, Builtin.functionEvaluator evalUnit)
        , (getKey, Builtin.functionEvaluator evalGet)
        , (updateKey, Builtin.functionEvaluator evalUpdate)
        , (inKey, Builtin.functionEvaluator evalIn)
        , (sizeKey, Builtin.functionEvaluator evalSize)
        , (makeKey, Builtin.functionEvaluator evalMake)
        , (updateAllKey, Builtin.functionEvaluator evalUpdateAll)
        ]

{- | Simplify the conjunction or equality of two concrete List domain values.

    When it is used for simplifying equality, one should separately solve the
    case ⊥ = ⊥. One should also throw away the term in the returned pattern.

    The lists are assumed to have the same sort, but this is not checked. If
    multiple lists are hooked to the same builtin domain, the verifier should
    reject the definition.
-}
unifyEquals ::
    forall unifier.
    MonadUnify unifier =>
    ( TermLike RewritingVariableName ->
      TermLike RewritingVariableName ->
      unifier (Pattern RewritingVariableName)
    ) ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    MaybeT unifier (Pattern RewritingVariableName)
unifyEquals
    simplifyChild
    first
    second =
        do
            tools <- Simplifier.askMetadataTools
            (Monad.guard . fromMaybe False) (isListSort tools sort1)
            unifyEquals0 (normalize first) (normalize second)
      where
        sort1 = termLikeSort first

        propagateConditions ::
            InternalVariable variable =>
            Traversable t =>
            t (Conditional variable a) ->
            Conditional variable (t a)
        propagateConditions = sequenceA

        unifyEquals0 ::
            TermLike RewritingVariableName ->
            TermLike RewritingVariableName ->
            MaybeT unifier (Pattern RewritingVariableName)

        unifyEquals0 pat1@(ElemVar_ _) pat2
            | TermLike.isFunctionPattern pat2 =
                lift $ simplifyChild pat1 pat2
            | otherwise = empty
        unifyEquals0 pat1 pat2@(ElemVar_ _)
            | TermLike.isFunctionPattern pat1 =
                lift $ simplifyChild pat1 pat2
            | otherwise = empty
        unifyEquals0 (App_ symbol1 args1) (App_ symbol2 args2)
            | isSymbolConcat symbol1
              , isSymbolConcat symbol2 =
                case (args1, args2) of
                    ( [InternalList_ builtin1, x1@(Var_ _)]
                        , [InternalList_ builtin2, x2@(Var_ _)]
                        ) ->
                            unifyEqualsFramedRightRight
                                symbol2
                                builtin1
                                x1
                                builtin2
                                x2
                                & lift
                    ( [x1@(Var_ _), InternalList_ builtin1]
                        , [x2@(Var_ _), InternalList_ builtin2]
                        ) ->
                            unifyEqualsFramedLeftLeft
                                symbol2
                                x1
                                builtin1
                                x2
                                builtin2
                                & lift
                    _ -> empty
        unifyEquals0 (InternalList_ builtin1) pat2 =
            case pat2 of
                InternalList_ builtin2 ->
                    lift $ unifyEqualsConcrete builtin1 builtin2
                (App_ symbol2 args2)
                    | isSymbolConcat symbol2 ->
                        case args2 of
                            [InternalList_ builtin2, x@(Var_ _)] ->
                                unifyEqualsFramedRight builtin1 builtin2 x & lift
                            [x@(Var_ _), InternalList_ builtin2] ->
                                unifyEqualsFramedLeft builtin1 x builtin2 & lift
                            [_, _] -> empty
                            _ -> Builtin.wrongArity concatKey
                    | otherwise -> empty
                _ -> empty
        unifyEquals0 pat1 pat2 =
            case pat2 of
                dv@(InternalList_ _) -> unifyEquals0 dv pat1
                _ -> empty

        unifyEqualsConcrete ::
            InternalList (TermLike RewritingVariableName) ->
            InternalList (TermLike RewritingVariableName) ->
            unifier (Pattern RewritingVariableName)
        unifyEqualsConcrete builtin1 builtin2
            | Seq.length list1 /= Seq.length list2 = bottomWithExplanation
            | otherwise = do
                tools <- Simplifier.askMetadataTools
                Reflection.give tools $ do
                    unified <- sequence $ Seq.zipWith simplifyChild list1 list2
                    let propagatedUnified = propagateConditions unified
                        result =
                            TermLike.markSimplified
                                . asInternal tools internalListSort
                                <$> propagatedUnified
                    return result
          where
            InternalList{internalListSort} = builtin1
            InternalList{internalListChild = list1} = builtin1
            InternalList{internalListChild = list2} = builtin2

        unifyEqualsFramedRight ::
            InternalList (TermLike RewritingVariableName) ->
            InternalList (TermLike RewritingVariableName) ->
            TermLike RewritingVariableName ->
            unifier (Pattern RewritingVariableName)
        unifyEqualsFramedRight
            internal1
            internal2
            frame2
                | Seq.length prefix2 > Seq.length list1 = bottomWithExplanation
                | otherwise =
                    do
                        tools <- Simplifier.askMetadataTools
                        let listSuffix1 = asInternal tools internalListSort suffix1
                        prefixUnified <-
                            unifyEqualsConcrete
                                internal1{internalListChild = prefix1}
                                internal2
                        suffixUnified <- simplifyChild frame2 listSuffix1
                        let result =
                                TermLike.markSimplified (mkInternalList internal1)
                                    <$ prefixUnified
                                    <* suffixUnified
                        return result
              where
                InternalList{internalListSort} = internal1
                InternalList{internalListChild = list1} = internal1
                InternalList{internalListChild = prefix2} = internal2
                (prefix1, suffix1) = Seq.splitAt prefixLength list1
                  where
                    prefixLength = Seq.length prefix2

        unifyEqualsFramedLeft ::
            InternalList (TermLike RewritingVariableName) ->
            TermLike RewritingVariableName ->
            InternalList (TermLike RewritingVariableName) ->
            unifier (Pattern RewritingVariableName)
        unifyEqualsFramedLeft
            internal1
            frame2
            internal2
                | Seq.length suffix2 > Seq.length list1 = bottomWithExplanation
                | otherwise =
                    do
                        tools <- Simplifier.askMetadataTools
                        let listPrefix1 = asInternal tools internalListSort prefix1
                        prefixUnified <- simplifyChild frame2 listPrefix1
                        suffixUnified <-
                            unifyEqualsConcrete
                                internal1{internalListChild = suffix1}
                                internal2
                        let result =
                                mkInternalList internal1
                                    <$ prefixUnified
                                    <* suffixUnified
                        return result
              where
                InternalList{internalListSort} = internal1
                InternalList{internalListChild = list1} = internal1
                InternalList{internalListChild = suffix2} = internal2
                (prefix1, suffix1) = Seq.splitAt prefixLength list1
                  where
                    prefixLength = Seq.length list1 - Seq.length suffix2
        bottomWithExplanation = do
            debugUnifyBottom
                "Cannot unify lists of different length."
                first
                second
            return Pattern.bottom

        unifyEqualsFramedRightRight ::
            TermLike.Symbol ->
            InternalList (TermLike RewritingVariableName) ->
            TermLike RewritingVariableName ->
            InternalList (TermLike RewritingVariableName) ->
            TermLike RewritingVariableName ->
            unifier (Pattern RewritingVariableName)
        unifyEqualsFramedRightRight
            symbol
            internal1
            frame1
            internal2
            frame2
                | length1 < length2 = do
                    tools <- Simplifier.askMetadataTools
                    prefixUnified <-
                        unifyEqualsConcrete
                            internal1
                            internal2{internalListChild = prefix2}
                    let listSuffix2 = asInternal tools internalListSort suffix2
                        suffix2Frame2 = mkApplySymbol symbol [listSuffix2, frame2]
                    suffixUnified <-
                        simplifyChild
                            frame1
                            suffix2Frame2
                    let result =
                            TermLike.markSimplified initial
                                <$ prefixUnified
                                <* suffixUnified
                    return result
                | length1 == length2 = do
                    prefixUnified <-
                        unifyEqualsConcrete internal1 internal2
                    suffixUnified <- simplifyChild frame1 frame2
                    let result =
                            TermLike.markSimplified initial
                                <$ prefixUnified
                                <* suffixUnified
                    return result
                | otherwise =
                    unifyEqualsFramedRightRight symbol internal2 frame2 internal1 frame1
              where
                initial = mkApplySymbol symbol [mkInternalList internal1, frame1]
                InternalList{internalListSort} = internal1
                InternalList{internalListChild = list1} = internal1
                InternalList{internalListChild = list2} = internal2
                length1 = Seq.length list1
                length2 = Seq.length list2
                (prefix2, suffix2) = Seq.splitAt length1 list2

        unifyEqualsFramedLeftLeft ::
            TermLike.Symbol ->
            TermLike RewritingVariableName ->
            InternalList (TermLike RewritingVariableName) ->
            TermLike RewritingVariableName ->
            InternalList (TermLike RewritingVariableName) ->
            unifier (Pattern RewritingVariableName)
        unifyEqualsFramedLeftLeft
            symbol
            frame1
            internal1
            frame2
            internal2
                | length1 < length2 = do
                    tools <- Simplifier.askMetadataTools
                    let listPrefix2 = asInternal tools internalListSort prefix2
                        frame2Prefix2 = mkApplySymbol symbol [frame2, listPrefix2]
                    prefixUnified <- simplifyChild frame1 frame2Prefix2
                    suffixUnified <-
                        unifyEqualsConcrete
                            internal1
                            internal2{internalListChild = suffix2}
                    let result =
                            TermLike.markSimplified initial <$ prefixUnified <* suffixUnified
                    return result
                | length1 == length2 = do
                    prefixUnified <- simplifyChild frame1 frame2
                    suffixUnified <- unifyEqualsConcrete internal1 internal2
                    let result =
                            TermLike.markSimplified initial
                                <$ prefixUnified
                                <* suffixUnified
                    return result
                | otherwise =
                    unifyEqualsFramedLeftLeft symbol frame2 internal2 frame1 internal1
              where
                initial = mkApplySymbol symbol [frame1, mkInternalList internal1]
                InternalList{internalListSort} = internal1
                InternalList{internalListChild = list1} = internal1
                InternalList{internalListChild = list2} = internal2
                length1 = Seq.length list1
                length2 = Seq.length list2
                (prefix2, suffix2) = Seq.splitAt (length2 - length1) list2

{- Normalizes a list expression.

Currently it only removes empty lists from concatenations.
-}
normalize :: InternalVariable variable => TermLike variable -> TermLike variable
normalize term@(App_ appHead children)
    | isSymbolConcat appHead =
        case map normalize children of
            [App_ childHead1 _, child2]
                | isSymbolUnit childHead1 -> child2
            [child1, App_ childHead2 _]
                | isSymbolUnit childHead2 -> child1
            normalizedChildren
                | normalizedChildren == children -> term
                | otherwise -> mkApplySymbol appHead normalizedChildren
normalize term = term
