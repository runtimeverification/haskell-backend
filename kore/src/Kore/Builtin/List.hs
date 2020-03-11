{- |
Module      : Kore.Builtin.List
Description : Built-in associative lists
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com
Stability   : experimental
Portability : portable

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.List as List
@
 -}
module Kore.Builtin.List
    ( sort
    , assertSort
    , verifiers
    , builtinFunctions
    , Builtin
    , returnList
    , asPattern
    , asInternal
    , asTermLike
    , internalize
      -- * Symbols
    , lookupSymbolGet
    , isSymbolConcat
    , isSymbolElement
    , isSymbolUnit
    , unifyEquals
      -- * keys
    , concatKey
    , elementKey
    , unitKey
    , getKey
    -- * Evaluators
    , evalConcat
    , evalElement
    , evalUnit
    , expectConcreteBuiltinList
    ) where

import Prelude.Kore

import Control.Error
    ( MaybeT
    , fromMaybe
    , hoistMaybe
    )
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans.Maybe as Monad.Trans.Maybe
    ( mapMaybeT
    )
import Data.Functor
    ( (<$)
    )
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import qualified Data.Reflection as Reflection
import Data.Sequence
    ( Seq
    )
import qualified Data.Sequence as Seq
import Data.Text
    ( Text
    )
import qualified Data.Text as Text

import qualified Kore.Builtin.Bool as Bool
import Kore.Builtin.Builtin
    ( acceptAnySort
    )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import Kore.Builtin.List.List
import qualified Kore.Domain.Builtin as Domain
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
    ( pattern App_
    , Builtin
    , pattern Builtin_
    , Concrete
    , pattern ElemVar_
    , InternalVariable
    , Sort
    , TermLike
    , pattern Var_
    , mkApplySymbol
    , mkBuiltin
    , mkSort
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
    ( isFunctionPattern
    , markSimplified
    )
import Kore.Step.Simplification.SimplificationType
    ( SimplificationType
    )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Syntax.Sentence
    ( SentenceSort (..)
    )
import Kore.Unification.Unify
    ( MonadUnify
    )
import qualified Kore.Unification.Unify as Monad.Unify

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
    HashMap.fromList [ (sort, verifySortDecl) ]
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
        SentenceSort { sentenceSortName } = sentenceSort
        expectedSort = mkSort sentenceSortName

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [ ( concatKey
      , Builtin.verifySymbol assertSort [assertSort , assertSort]
      )
    , ( elementKey
      , Builtin.verifySymbol assertSort [acceptAnySort]
      )
    , ( unitKey
      , Builtin.verifySymbol assertSort []
      )
    , ( getKey
      , Builtin.verifySymbol acceptAnySort [assertSort, Int.assertSort]
      )
    , ( updateKey
      , Builtin.verifySymbol assertSort
            [assertSort, Int.assertSort, acceptAnySort]
      )
    , ( inKey
      , Builtin.verifySymbol Bool.assertSort [acceptAnySort, assertSort]
      )
    , ( sizeKey
      , Builtin.verifySymbol Int.assertSort [assertSort]
      )
    ]

{- | Abort function evaluation if the argument is not a List domain value.

    If the operand pattern is not a domain value, the function is simply
    'NotApplicable'. If the operand is a domain value, but not represented
    by a 'BuiltinDomainList', it is a bug.

 -}
expectBuiltinList
    :: Monad m
    => Text  -- ^ Context for error message
    -> TermLike variable  -- ^ Operand pattern
    -> MaybeT m (Seq (TermLike variable))
expectBuiltinList ctx =
    \case
        Builtin_ domain ->
            case domain of
                Domain.BuiltinList Domain.InternalList { builtinListChild } ->
                    return builtinListChild
                _ ->
                    Builtin.verifierBug
                    $ Text.unpack ctx ++ ": Domain value is not a list"
        _ -> empty

expectConcreteBuiltinList
    :: Ord variable
    => Monad m
    => Text  -- ^ Context for error message
    -> TermLike variable  -- ^ Operand pattern
    -> MaybeT m (Seq (TermLike Concrete))
expectConcreteBuiltinList ctx =
    Monad.Trans.Maybe.mapMaybeT (fmap Monad.join)
        . fmap (traverse Builtin.toKey)
        . expectBuiltinList ctx

returnList
    :: (MonadSimplify m, InternalVariable variable)
    => Sort
    -> Seq (TermLike variable)
    -> m (AttemptedAxiom variable)
returnList builtinListSort builtinListChild = do
    tools <- Simplifier.askMetadataTools
    Builtin.appliedFunction
        $ Reflection.give tools
        $ asPattern builtinListSort builtinListChild

evalElement :: Builtin.Function
evalElement =
    Builtin.functionEvaluator evalElement0
  where
    evalElement0 resultSort =
        \case
            [elem'] -> returnList resultSort (Seq.singleton elem')
            _ -> Builtin.wrongArity elementKey

evalGet :: Builtin.Function
evalGet =
    Builtin.functionEvaluator evalGet0
  where
    evalGet0 :: Builtin.FunctionImplementation
    evalGet0 _ = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_list, _ix) =
                    case arguments of
                        [_list, _ix] -> (_list, _ix)
                        _ -> Builtin.wrongArity getKey
                emptyList = do
                    _list <- expectBuiltinList getKey _list
                    if Seq.null _list
                        then Builtin.appliedFunction Pattern.bottom
                        else empty
                bothConcrete = do
                    _list <- expectBuiltinList getKey _list
                    _ix <- fromInteger <$> Int.expectBuiltinInt getKey _ix
                    let ix
                            | _ix < 0 =
                                -- negative indices count from end of list
                                _ix + Seq.length _list
                            | otherwise = _ix
                    (Builtin.appliedFunction . maybeBottom)
                        (Seq.lookup ix _list)
            emptyList <|> bothConcrete
      where
        maybeBottom =
            maybe Pattern.bottom Pattern.fromTermLike

evalUpdate :: Builtin.Function
evalUpdate =
    Builtin.functionEvaluator evalUpdate0
  where
    evalUpdate0 :: Builtin.FunctionImplementation
    evalUpdate0 resultSort [_list, _ix, value] =
        Builtin.getAttemptedAxiom $ do
            _list <- expectBuiltinList getKey _list
            _ix <- fromInteger <$> Int.expectBuiltinInt getKey _ix
            let len = Seq.length _list
                ix
                  | _ix < 0 =
                    -- negative indices count from end of list
                    _ix + len
                  | otherwise = _ix
            if ix >= 0 && ix < len
                then returnList resultSort (Seq.update ix value _list)
                else Builtin.appliedFunction Pattern.bottom
    evalUpdate0 _ _ = Builtin.wrongArity updateKey

evalIn :: Builtin.Function
evalIn =
    Builtin.functionEvaluator evalIn0
  where
    evalIn0 :: Builtin.FunctionImplementation
    evalIn0 resultSort [_elem, _list] =
        Builtin.getAttemptedAxiom $ do
            _list <- expectConcreteBuiltinList inKey _list
            _elem <- hoistMaybe $ Builtin.toKey _elem
            Builtin.appliedFunction
                $ Bool.asPattern resultSort
                $ _elem `elem` _list
    evalIn0 _ _ = Builtin.wrongArity inKey

evalUnit :: Builtin.Function
evalUnit =
    Builtin.functionEvaluator evalUnit0
  where
    evalUnit0 resultSort =
        \case
            [] -> returnList resultSort Seq.empty
            _ -> Builtin.wrongArity "LIST.unit"

evalConcat :: Builtin.Function
evalConcat =
    Builtin.functionEvaluator evalConcat0
  where
    evalConcat0
        :: (InternalVariable variable, MonadSimplify simplifier)
        => Sort
        -> [TermLike variable]
        -> simplifier (AttemptedAxiom variable)
    evalConcat0 resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_list1, _list2) =
                    case arguments of
                        [_list1, _list2] -> (_list1, _list2)
                        _ -> Builtin.wrongArity concatKey
                leftIdentity = do
                    _list1 <- expectBuiltinList concatKey _list1
                    if Seq.null _list1
                        then
                            Builtin.appliedFunction
                            $ Pattern.fromTermLike _list2
                        else
                            empty
                rightIdentity = do
                    _list2 <- expectBuiltinList concatKey _list2
                    if Seq.null _list2
                        then
                            Builtin.appliedFunction
                            $ Pattern.fromTermLike _list1
                        else
                            empty
                bothConcrete = do
                    _list1 <- expectBuiltinList concatKey _list1
                    _list2 <- expectBuiltinList concatKey _list2
                    returnList resultSort (_list1 <> _list2)
            leftIdentity <|> rightIdentity <|> bothConcrete

evalSize :: Builtin.Function
evalSize =
    Builtin.functionEvaluator evalSize0
  where
    evalSize0 :: Builtin.FunctionImplementation
    evalSize0 resultSort [_list] =
        Builtin.getAttemptedAxiom $ do
            _list <- expectBuiltinList sizeKey _list
            Seq.length _list
                & fromIntegral & Int.asPattern resultSort
                & Builtin.appliedFunction
    evalSize0 _ _ = Builtin.wrongArity sizeKey

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
        [ (concatKey, evalConcat)
        , (elementKey, evalElement)
        , (unitKey, evalUnit)
        , (getKey, evalGet)
        , (updateKey, evalUpdate)
        , (inKey, evalIn)
        , (sizeKey, evalSize)
        ]

{- | Simplify the conjunction or equality of two concrete List domain values.

    When it is used for simplifying equality, one should separately solve the
    case ⊥ = ⊥. One should also throw away the term in the returned pattern.

    The lists are assumed to have the same sort, but this is not checked. If
    multiple lists are hooked to the same builtin domain, the verifier should
    reject the definition.
 -}
unifyEquals
    :: forall variable unifier
    .  (InternalVariable variable, MonadUnify unifier)
    => SimplificationType
    -> (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
unifyEquals
    simplificationType
    simplifyChild
    first
    second
  = do
    tools <- Simplifier.askMetadataTools
    (Monad.guard . fromMaybe False) (isListSort tools sort1)
    unifyEquals0 (normalize first) (normalize second)
  where
    sort1 = termLikeSort first

    propagateConditions
        :: Traversable t
        => t (Conditional variable a)
        -> Conditional variable (t a)
    propagateConditions = sequenceA

    unifyEquals0
        :: TermLike variable
        -> TermLike variable
        -> MaybeT unifier (Pattern variable)

    unifyEquals0 pat1@(ElemVar_ _) pat2
      | TermLike.isFunctionPattern pat2 =
        lift $ simplifyChild pat1 pat2
      | otherwise = empty

    unifyEquals0 pat1 pat2@(ElemVar_ _)
      | TermLike.isFunctionPattern pat1 =
        lift $ simplifyChild pat1 pat2
      | otherwise = empty

    unifyEquals0 dv1@(Builtin_ (Domain.BuiltinList builtin1)) pat2 =
        case pat2 of
            dv2@(Builtin_ child2)
              | Domain.BuiltinList builtin2 <- child2 ->
                lift $ unifyEqualsConcrete builtin1 builtin2
              | otherwise ->
                (error . unlines)
                    [ "Cannot unify a builtin List domain value:"
                    , show dv1
                    , "with:"
                    , show dv2
                    , "This should have been a sort error."
                    ]
            app@(App_ symbol2 args2)
              | isSymbolConcat symbol2 ->
                lift $ case args2 of
                    [ Builtin_ (Domain.BuiltinList builtin2), x@(Var_ _) ] ->
                        unifyEqualsFramedRight builtin1 builtin2 x
                    [ x@(Var_ _), Builtin_ (Domain.BuiltinList builtin2) ] ->
                        unifyEqualsFramedLeft builtin1 x builtin2
                    [ _, _ ] ->
                        Builtin.unifyEqualsUnsolved
                            simplificationType
                            dv1
                            app
                    _ -> Builtin.wrongArity concatKey
              | otherwise -> empty
            _ -> empty

    unifyEquals0 pat1 pat2 =
        case pat2 of
            dv@(Builtin_ (Domain.BuiltinList _)) -> unifyEquals0 dv pat1
            _ -> empty

    unifyEqualsConcrete
        :: Domain.InternalList (TermLike variable)
        -> Domain.InternalList (TermLike variable)
        -> unifier (Pattern variable)
    unifyEqualsConcrete builtin1 builtin2
      | Seq.length list1 /= Seq.length list2 = bottomWithExplanation
      | otherwise = do
        tools <- Simplifier.askMetadataTools
        Reflection.give tools $ do
            unified <- sequence $ Seq.zipWith simplifyChild list1 list2
            let
                propagatedUnified = propagateConditions unified
                result =
                    TermLike.markSimplified
                    . asInternal tools builtinListSort
                    <$> propagatedUnified
            return result
      where
        Domain.InternalList { builtinListSort } = builtin1
        Domain.InternalList { builtinListChild = list1 } = builtin1
        Domain.InternalList { builtinListChild = list2 } = builtin2

    unifyEqualsFramedRight
        :: Domain.InternalList (TermLike variable)
        -> Domain.InternalList (TermLike variable)
        -> TermLike variable
        -> unifier (Pattern variable)
    unifyEqualsFramedRight
        builtin1
        builtin2
        frame2
      | Seq.length prefix2 > Seq.length list1 = bottomWithExplanation
      | otherwise =
        do
            tools <- Simplifier.askMetadataTools
            let listSuffix1 = asInternal tools builtinListSort suffix1
            prefixUnified <-
                unifyEqualsConcrete
                    builtin1 { Domain.builtinListChild = prefix1 }
                    builtin2
            suffixUnified <- simplifyChild frame2 listSuffix1
            let result = TermLike.markSimplified (mkBuiltin internal1)
                    <$ prefixUnified <* suffixUnified
            return result
      where
        internal1 = Domain.BuiltinList builtin1
        Domain.InternalList { builtinListSort } = builtin1
        Domain.InternalList { builtinListChild = list1 } = builtin1
        Domain.InternalList { builtinListChild = prefix2 } = builtin2
        (prefix1, suffix1) = Seq.splitAt prefixLength list1
          where
            prefixLength = Seq.length prefix2

    unifyEqualsFramedLeft
        :: Domain.InternalList (TermLike variable)
        -> TermLike variable
        -> Domain.InternalList (TermLike variable)
        -> unifier (Pattern variable)
    unifyEqualsFramedLeft
        builtin1
        frame2
        builtin2
      | Seq.length suffix2 > Seq.length list1 = bottomWithExplanation
      | otherwise =
        do
            tools <- Simplifier.askMetadataTools
            let listPrefix1 = asInternal tools builtinListSort prefix1
            prefixUnified <- simplifyChild frame2 listPrefix1
            suffixUnified <-
                unifyEqualsConcrete
                    builtin1 { Domain.builtinListChild = suffix1 }
                    builtin2
            let result = mkBuiltin internal1 <$ prefixUnified <* suffixUnified
            return result
      where
        internal1 = Domain.BuiltinList builtin1
        Domain.InternalList { builtinListSort } = builtin1
        Domain.InternalList { builtinListChild = list1 } = builtin1
        Domain.InternalList { builtinListChild = suffix2 } = builtin2
        (prefix1, suffix1) = Seq.splitAt prefixLength list1
          where
            prefixLength = Seq.length list1 - Seq.length suffix2
    bottomWithExplanation = do
        Monad.Unify.explainBottom
            "Cannot unify lists of different length."
            first
            second
        return Pattern.bottom

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
