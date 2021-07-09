{- |
Module      : Kore.Builtin.Set
Description : Built-in sets
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : thomas.tuegel@runtimeverification.com

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Set as Set
@
-}
module Kore.Builtin.Set (
    sort,
    assertSort,
    isSetSort,
    verifiers,
    builtinFunctions,
    returnConcreteSet,
    internalize,
    expectBuiltinSet,
    expectConcreteBuiltinSet,
    evalConcat,
    evalElement,
    evalUnit,
    evalDifference,

    -- * Unification
    unifyEquals,
) where

import Control.Error (
    MaybeT (MaybeT),
    hoistMaybe,
    runMaybeT,
 )
import qualified Control.Monad as Monad
import Data.HashMap.Strict (
    HashMap,
 )
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import Data.Text (
    Text,
 )
import qualified Kore.Attribute.Symbol as Attribute (
    Symbol,
 )
import qualified Kore.Builtin.AssociativeCommutative as Ac
import Kore.Builtin.Attributes (
    isConstructorModulo_,
 )
import qualified Kore.Builtin.Bool as Bool
import Kore.Builtin.Builtin (
    acceptAnySort,
 )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import qualified Kore.Builtin.List as List
import qualified Kore.Builtin.Set.Set as Set
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.Internal.ApplicationSorts (
    ApplicationSorts (..),
 )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.InternalSet
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeCeilPredicate,
    makeMultipleAndPredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike (
    Key,
    TermLike,
    mkSort,
    retractKey,
    termLikeSort,
    pattern App_,
    pattern InternalSet_,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Log.DebugUnifyBottom (
    debugUnifyBottomAndReturnBottom,
 )
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Sort (
    Sort,
 )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Syntax.Sentence (
    SentenceSort (SentenceSort),
 )
import qualified Kore.Syntax.Sentence as Sentence.DoNotUse (
    SentenceSort (..),
 )
import Kore.Unification.Unify (
    MonadUnify,
 )
import qualified Kore.Unification.Unify as Monad.Unify
import Prelude.Kore

-- | Builtin name of the @Set@ sort.
sort :: Text
sort = "SET.Set"

{- | Is the given sort hooked to the builtin Set sort?

Returns Nothing if the sort is unknown (i.e. the _PREDICATE sort).
Returns Just False if the sort is a variable.
-}
isSetSort :: SmtMetadataTools attrs -> Sort -> Maybe Bool
isSetSort = Builtin.isSort sort

{- | Verify that the sort is hooked to the builtin @Set@ sort.

  See also: 'sort', 'Builtin.verifySort'
-}
assertSort :: Builtin.SortVerifier
assertSort = Builtin.verifySort sort

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
        Builtin.assertSymbolHook indexedModule unitId Set.unitKey
        Builtin.assertSymbolResultSort indexedModule unitId expectedSort
        elementId <- Builtin.getElementId attrs
        Builtin.assertSymbolHook indexedModule elementId Set.elementKey
        Builtin.assertSymbolResultSort indexedModule elementId expectedSort
        concatId <- Builtin.getConcatId attrs
        Builtin.assertSymbolHook indexedModule concatId Set.concatKey
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
            ( Set.concatKey
            , Builtin.verifySymbol assertSort [assertSort, assertSort]
            )
        ,
            ( Set.elementKey
            , Builtin.verifySymbol assertSort [acceptAnySort]
            )
        ,
            ( Set.unitKey
            , Builtin.verifySymbol assertSort []
            )
        ,
            ( Set.inKey
            , Builtin.verifySymbol Bool.assertSort [acceptAnySort, assertSort]
            )
        ,
            ( Set.differenceKey
            , Builtin.verifySymbol assertSort [assertSort, assertSort]
            )
        ,
            ( Set.toListKey
            , Builtin.verifySymbol List.assertSort [assertSort]
            )
        ,
            ( Set.sizeKey
            , Builtin.verifySymbol Int.assertSort [assertSort]
            )
        ,
            ( Set.intersectionKey
            , Builtin.verifySymbol assertSort [assertSort, assertSort]
            )
        ,
            ( Set.list2setKey
            , Builtin.verifySymbol assertSort [List.assertSort]
            )
        ,
            ( Set.inclusionKey
            , Builtin.verifySymbol Bool.assertSort [assertSort, assertSort]
            )
        ]

{- | Returns @empty@ if the argument is not a @NormalizedSet@ domain value.

Returns the @NormalizedSet@ otherwise.
-}
expectBuiltinSet ::
    MonadSimplify m =>
    -- | Context for error message
    Text ->
    -- | Operand pattern
    TermLike variable ->
    MaybeT m (Ac.TermNormalizedAc NormalizedSet variable)
expectBuiltinSet _ (InternalSet_ internalSet) =
    return (builtinAcChild internalSet)
expectBuiltinSet _ _ = empty

{- | Returns @empty@ if the argument is not a @NormalizedSet@ domain value
which consists only of concrete elements.

Returns the @Set@ of concrete elements otherwise.
-}
expectConcreteBuiltinSet ::
    MonadSimplify m =>
    -- | Context for error message
    Text ->
    -- | Operand pattern
    TermLike variable ->
    MaybeT m (HashMap Key (SetValue (TermLike variable)))
expectConcreteBuiltinSet ctx _set = do
    _set <- expectBuiltinSet ctx _set
    case unwrapAc _set of
        NormalizedAc
            { elementsWithVariables = []
            , concreteElements
            , opaque = []
            } -> return concreteElements
        _ -> empty

expectEmptySet ::
    MonadSimplify m =>
    -- | Context for error message
    Text ->
    -- | Operand pattern
    TermLike variable ->
    MaybeT m ()
expectEmptySet cxt _set = do
    _set <- expectConcreteBuiltinSet cxt _set
    Monad.guard (HashMap.null _set)

{- | Converts a @Set@ of concrete elements to a @NormalizedSet@ and returns it
as a function result.
-}
returnConcreteSet ::
    (MonadSimplify m, InternalVariable variable) =>
    Sort ->
    HashMap Key (SetValue (TermLike variable)) ->
    m (Pattern variable)
returnConcreteSet = Ac.returnConcreteAc

evalElement :: Builtin.Function
evalElement _ resultSort [_elem] =
    case retractKey _elem of
        Just concrete ->
            TermLike.assertConstructorLikeKeys [_elem] $
                returnConcreteSet
                    resultSort
                    (HashMap.singleton concrete SetValue)
        Nothing ->
            (Ac.returnAc resultSort . wrapAc)
                NormalizedAc
                    { elementsWithVariables =
                        [SetElement _elem]
                    , concreteElements = HashMap.empty
                    , opaque = []
                    }
evalElement _ _ _ = Builtin.wrongArity Set.elementKey

evalIn :: Builtin.Function
evalIn _ resultSort [_elem, _set] = do
    let setSymbolic = do
            _elem <- hoistMaybe $ retractKey _elem
            _set' <- expectBuiltinSet Set.inKey _set
            let result = isConcreteKeyOfAc _elem _set'
            returnIfTrueAndDefined result _set
        bothSymbolic = do
            _set' <- expectBuiltinSet Set.inKey _set
            let result = isSymbolicKeyOfAc _elem _set'
            returnIfTrueAndDefined result _set
        emptySet = do
            expectEmptySet Set.inKey _set
            Monad.guard (TermLike.isFunctionalPattern _elem)
            return $ asExpandedBoolPattern False
        bothConcrete = do
            _elem <- hoistMaybe $ retractKey _elem
            _set <- expectConcreteBuiltinSet Set.inKey _set
            HashMap.member _elem _set
                & asExpandedBoolPattern
                & return
    setSymbolic <|> bothSymbolic <|> emptySet <|> bothConcrete
  where
    asExpandedBoolPattern = Bool.asPattern resultSort
    returnIfTrueAndDefined result setTerm
        | result = do
            let condition =
                    Conditional.fromPredicate $ makeCeilPredicate setTerm
                trueWithCondition =
                    Pattern.andCondition
                        (asExpandedBoolPattern result)
                        condition
            return trueWithCondition
        | otherwise = empty
evalIn _ _ _ = Builtin.wrongArity Set.inKey

evalUnit :: Builtin.Function
evalUnit _ resultSort =
    \case
        [] -> returnConcreteSet resultSort HashMap.empty
        _ -> Builtin.wrongArity Set.unitKey

evalConcat :: Builtin.Function
evalConcat _ resultSort [set1, set2] =
    Ac.evalConcatNormalizedOrBottom @NormalizedSet
        resultSort
        (Ac.toNormalized set1)
        (Ac.toNormalized set2)
evalConcat _ _ _ = Builtin.wrongArity Set.concatKey

evalDifference ::
    forall variable simplifier.
    InternalVariable variable =>
    MonadSimplify simplifier =>
    SideCondition variable ->
    TermLike.Application TermLike.Symbol (TermLike variable) ->
    MaybeT simplifier (Pattern variable)
evalDifference
    sideCondition
    ( TermLike.Application
            symbol@TermLike.Symbol{symbolSorts = ApplicationSorts _ resultSort}
            args@[_set1, _set2]
        ) =
        do
            let rightIdentity = do
                    _set2 <- expectConcreteBuiltinSet ctx _set2
                    if HashMap.null _set2
                        then return (Pattern.fromTermLike _set1)
                        else empty
                bothConcrete = do
                    _set1 <- expectConcreteBuiltinSet ctx _set1
                    _set2 <- expectConcreteBuiltinSet ctx _set2
                    returnConcreteSet resultSort (HashMap.difference _set1 _set2)
                symbolic = do
                    _set1 <- expectBuiltinSet ctx _set1
                    _set2 <- expectBuiltinSet ctx _set2
                    let definedArgs =
                            filter (not . SideCondition.isDefined sideCondition) args
                                & map makeCeilPredicate
                                & makeMultipleAndPredicate
                                & Conditional.fromPredicate
                    let NormalizedAc
                            { concreteElements = concrete1
                            , elementsWithVariables = symbolic1'
                            , opaque = opaque1'
                            } =
                                unwrapAc _set1
                        symbolic1 =
                            unwrapElement <$> symbolic1'
                                & HashMap.fromList
                        opaque1 = HashSet.fromList opaque1'
                    let NormalizedAc
                            { concreteElements = concrete2
                            , elementsWithVariables = symbolic2'
                            , opaque = opaque2'
                            } =
                                unwrapAc _set2
                        symbolic2 =
                            unwrapElement <$> symbolic2'
                                & HashMap.fromList
                        opaque2 = HashSet.fromList opaque2'
                    let set1' =
                            NormalizedAc
                                { concreteElements =
                                    HashMap.difference concrete1 concrete2
                                , elementsWithVariables =
                                    HashMap.difference symbolic1 symbolic2
                                        & HashMap.toList
                                        & map wrapElement
                                , opaque =
                                    HashSet.difference opaque1 opaque2 & HashSet.toList
                                }
                        set2' =
                            NormalizedAc
                                { concreteElements =
                                    HashMap.difference concrete2 concrete1
                                , elementsWithVariables =
                                    HashMap.difference symbolic2 symbolic1
                                        & HashMap.toList
                                        & map wrapElement
                                , opaque =
                                    HashSet.difference opaque1 opaque1 & HashSet.toList
                                }
                    pat1 <- Ac.returnAc resultSort (NormalizedSet set1')
                    pat2 <- Ac.returnAc resultSort (NormalizedSet set2')
                    let pat
                            | (not . nullAc) set1'
                              , (not . nullAc) set2' =
                                differenceSet <$> pat1 <*> pat2
                            | otherwise = pat1
                    return (Pattern.andCondition pat definedArgs)

            rightIdentity <|> bothConcrete <|> symbolic
      where
        ctx = Set.differenceKey
        differenceSet set1 set2 = TermLike.mkApplySymbol symbol [set1, set2]
evalDifference _ _ =
    Builtin.wrongArity Set.differenceKey

evalToList :: Builtin.Function
evalToList _ resultSort [_set] = do
    _set <- expectConcreteBuiltinSet Set.toListKey _set
    HashMap.keysSet _set
        & HashSet.toList
        & Seq.fromList
        & fmap (from @Key)
        & List.returnList resultSort
evalToList _ _ _ = Builtin.wrongArity Set.toListKey

evalSize :: Builtin.Function
evalSize _ resultSort [_set] = do
    _set <- expectConcreteBuiltinSet Set.sizeKey _set
    HashMap.size _set
        & toInteger
        & Int.asPattern resultSort
        & return
evalSize _ _ _ = Builtin.wrongArity Set.sizeKey

evalIntersection :: Builtin.Function
evalIntersection _ resultSort [_set1, _set2] = do
    _set1 <- expectConcreteBuiltinSet ctx _set1
    _set2 <- expectConcreteBuiltinSet ctx _set2
    returnConcreteSet resultSort (HashMap.intersection _set1 _set2)
  where
    ctx = Set.intersectionKey
evalIntersection _ _ _ = Builtin.wrongArity Set.intersectionKey

evalList2set :: Builtin.Function
evalList2set _ resultSort [_list] = do
    _list <- List.expectConcreteBuiltinList Set.list2setKey _list
    let _set =
            fmap (\x -> (x, SetValue)) _list
                & toList
                & HashMap.fromList
    returnConcreteSet resultSort _set
evalList2set _ _ _ = Builtin.wrongArity Set.list2setKey

evalInclusion :: Builtin.Function
evalInclusion _ resultSort [_setLeft, _setRight] = do
    _setLeft <- expectConcreteBuiltinSet Set.inclusionKey _setLeft
    _setRight <- expectConcreteBuiltinSet Set.inclusionKey _setRight
    HashMap.isSubmapOf _setLeft _setRight
        & Bool.asPattern resultSort
        & return
evalInclusion _ _ _ = Builtin.wrongArity Set.inclusionKey

-- | Implement builtin function evaluation.
builtinFunctions :: Map Text BuiltinAndAxiomSimplifier
builtinFunctions =
    Map.fromList
        [ (Set.concatKey, Builtin.functionEvaluator evalConcat)
        , (Set.elementKey, Builtin.functionEvaluator evalElement)
        , (Set.unitKey, Builtin.functionEvaluator evalUnit)
        , (Set.inKey, Builtin.functionEvaluator evalIn)
        , (Set.differenceKey, Builtin.applicationEvaluator evalDifference)
        , (Set.toListKey, Builtin.functionEvaluator evalToList)
        , (Set.sizeKey, Builtin.functionEvaluator evalSize)
        , (Set.intersectionKey, Builtin.functionEvaluator evalIntersection)
        , (Set.list2setKey, Builtin.functionEvaluator evalList2set)
        , (Set.inclusionKey, Builtin.functionEvaluator evalInclusion)
        ]

{- | Convert a Set-sorted 'TermLike' to its internal representation.

The 'TermLike' is unmodified if it is not Set-sorted. @internalize@ only
operates at the top-most level, it does not descend into the 'TermLike' to
internalize subterms.
-}
internalize ::
    InternalVariable variable =>
    SmtMetadataTools Attribute.Symbol ->
    TermLike variable ->
    TermLike variable
internalize tools termLike
    -- Ac.toNormalized is greedy about 'normalizing' opaque terms, we should only
    -- apply it if we know the term head is a constructor-like symbol.
    | App_ symbol _ <- termLike
      , isConstructorModulo_ symbol =
        case Ac.toNormalized @NormalizedSet termLike of
            Ac.Bottom -> TermLike.mkBottom sort'
            Ac.Normalized termNormalized
                | let unwrapped = unwrapAc termNormalized
                  , null (elementsWithVariables unwrapped)
                  , null (concreteElements unwrapped)
                  , [singleOpaqueTerm] <- opaque unwrapped ->
                    -- When the 'normalized' term consists of a single opaque Map-sorted
                    -- term, we should prefer to return only that term.
                    singleOpaqueTerm
                | otherwise -> Ac.asInternal tools sort' termNormalized
    | otherwise = termLike
  where
    sort' = termLikeSort termLike

{- | Simplify the conjunction or equality of two concrete Set domain values.

    When it is used for simplifying equality, one should separately solve the
    case ⊥ = ⊥. One should also throw away the term in the returned pattern.

    The sets are assumed to have the same sort, but this is not checked. If
    multiple sorts are hooked to the same builtin domain, the verifier should
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
    unifyEqualsChildren
    first
    second =
        do
            tools <- Simplifier.askMetadataTools
            (Monad.guard . fromMaybe False) (isSetSort tools sort1)
            MaybeT $ do
                unifiers <- Monad.Unify.gather (runMaybeT (unifyEquals0 first second))
                case sequence unifiers of
                    Nothing -> return Nothing
                    Just us -> Monad.Unify.scatter (map Just us)
      where
        sort1 = termLikeSort first

        unifyEquals0 ::
            TermLike RewritingVariableName ->
            TermLike RewritingVariableName ->
            MaybeT unifier (Pattern RewritingVariableName)
        unifyEquals0 (InternalSet_ normalized1) (InternalSet_ normalized2) = do
            tools <- Simplifier.askMetadataTools
            Ac.unifyEqualsNormalized
                tools
                first
                second
                unifyEqualsChildren
                normalized1
                normalized2
        unifyEquals0 pat1 pat2 = do
            firstDomain <- asDomain pat1
            secondDomain <- asDomain pat2
            unifyEquals0 firstDomain secondDomain
          where
            asDomain ::
                TermLike RewritingVariableName ->
                MaybeT unifier (TermLike RewritingVariableName)
            asDomain patt =
                case normalizedOrBottom of
                    Ac.Normalized normalized -> do
                        tools <- Simplifier.askMetadataTools
                        return (Ac.asInternal tools sort1 normalized)
                    Ac.Bottom ->
                        lift $
                            debugUnifyBottomAndReturnBottom
                                "Duplicated elements in normalization."
                                first
                                second
              where
                normalizedOrBottom ::
                    Ac.NormalizedOrBottom NormalizedSet RewritingVariableName
                normalizedOrBottom = Ac.toNormalized patt
