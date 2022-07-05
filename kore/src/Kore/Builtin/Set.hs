{- |
Module      : Kore.Builtin.Set
Description : Built-in sets
Copyright   : (c) Runtime Verification, 2018-2021
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
    matchUnifyEquals,
) where

import Control.Error (
    MaybeT,
    hoistMaybe,
 )
import Control.Monad qualified as Monad
import Data.HashMap.Strict (
    HashMap,
 )
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Data.Map.Strict (
    Map,
 )
import Data.Map.Strict qualified as Map
import Data.Sequence qualified as Seq
import Data.Text (
    Text,
 )
import Kore.Attribute.Symbol qualified as Attribute (
    Symbol,
 )
import Kore.Builtin.AssociativeCommutative qualified as Ac
import Kore.Builtin.Attributes (
    isConstructorModulo_,
 )
import Kore.Builtin.Bool qualified as Bool
import Kore.Builtin.Builtin (
    acceptAnySort,
 )
import Kore.Builtin.Builtin qualified as Builtin
import Kore.Builtin.Int qualified as Int
import Kore.Builtin.List qualified as List
import Kore.Builtin.Set.Set qualified as Set
import Kore.IndexedModule.IndexedModule (
    IndexedModule (..),
 )
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import Kore.Internal.ApplicationSorts (
    ApplicationSorts (..),
 )
import Kore.Internal.Conditional qualified as Conditional
import Kore.Internal.InternalSet
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (
    makeCeilPredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.TermLike (
    Key,
    TermLike,
    mkSort,
    retractKey,
    termLikeSort,
    pattern App_,
    pattern InternalSet_,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Log.DebugUnifyBottom (
    debugUnifyBottomAndReturnBottom,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify as Simplifier
import Kore.Sort (
    Sort,
 )
import Kore.Syntax.Sentence (
    SentenceSort (SentenceSort),
 )
import Kore.Syntax.Sentence qualified as Sentence.DoNotUse (
    SentenceSort (..),
 )
import Kore.Unification.Unify (
    MonadUnify,
 )
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
        Builtin.assertSymbolHook syntax unitId Set.unitKey
        Builtin.assertSymbolResultSort syntax unitId expectedSort
        elementId <- Builtin.getElementId attrs
        Builtin.assertSymbolHook syntax elementId Set.elementKey
        Builtin.assertSymbolResultSort syntax elementId expectedSort
        concatId <- Builtin.getConcatId attrs
        Builtin.assertSymbolHook syntax concatId Set.concatKey
        Builtin.assertSymbolResultSort syntax concatId expectedSort
        return ()
      where
        SentenceSort{sentenceSortName} = sentenceSort
        expectedSort = mkSort sentenceSortName
        syntax = indexedModuleSyntax indexedModule

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
    _
    ( TermLike.Application
            TermLike.Symbol{symbolSorts = ApplicationSorts _ resultSort}
            [_set1, _set2]
        ) = do
        _set1 <- expectConcreteBuiltinSet ctx _set1
        _set2 <- expectConcreteBuiltinSet ctx _set2
        returnConcreteSet resultSort (HashMap.difference _set1 _set2)
      where
        ctx = Set.differenceKey
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

data NormAcData = NormAcData
    { normalized1, normalized2 :: !(InternalSet Key (TermLike RewritingVariableName))
    , term1, term2 :: !(TermLike RewritingVariableName)
    , acData :: !(Ac.UnifyEqualsNormAc NormalizedSet RewritingVariableName)
    }

data UnifyEqualsMap
    = ReturnBottom !(TermLike RewritingVariableName) !(TermLike RewritingVariableName)
    | NormAc !NormAcData

-- | Matches two concrete Set domain values.
matchUnifyEquals ::
    SmtMetadataTools Attribute.Symbol ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Maybe UnifyEqualsMap
matchUnifyEquals tools first second
    | Just True <- isSetSort tools sort1 =
        worker first second True <|> worker second first False
    | otherwise = Nothing
  where
    sort1 = termLikeSort first

    normalizedOrBottom ::
        TermLike RewritingVariableName ->
        Ac.NormalizedOrBottom NormalizedSet RewritingVariableName
    normalizedOrBottom = Ac.toNormalized

    worker a b isFirstMatched
        | InternalSet_ normalized1 <- a
          , InternalSet_ normalized2 <- b =
            NormAc . NormAcData normalized1 normalized2 term1 term2
                <$> Ac.matchUnifyEqualsNormalizedAc
                    tools
                    normalized1
                    normalized2
        | otherwise = case normalizedOrBottom a of
            Ac.Bottom -> Just $ ReturnBottom term1 term2
            Ac.Normalized normalized1 ->
                let a' = Ac.asInternal tools sort1 normalized1
                 in case normalizedOrBottom b of
                        Ac.Bottom -> Just $ ReturnBottom term1 term2
                        Ac.Normalized normalized2 ->
                            let b' = Ac.asInternal tools sort1 normalized2
                             in worker a' b' isFirstMatched
      where
        (term1, term2) = if isFirstMatched then (a, b) else (b, a)

{- | Simplify the conjunction or equality of two concrete Map domain values.

When it is used for simplifying equality, one should separately solve the
case ⊥ = ⊥. One should also throw away the term in the returned pattern.

The maps are assumed to have the same sort, but this is not checked. If
multiple sorts are hooked to the same builtin domain, the verifier should
reject the definition.
-}
unifyEquals ::
    forall unifier.
    MonadUnify unifier =>
    TermSimplifier RewritingVariableName unifier ->
    SmtMetadataTools Attribute.Symbol ->
    UnifyEqualsMap ->
    unifier (Pattern RewritingVariableName)
unifyEquals unifyEqualsChildren tools unifyData =
    case unifyData of
        ReturnBottom term1 term2 ->
            debugUnifyBottomAndReturnBottom
                "Duplicated elements in normalization."
                term1
                term2
        NormAc unifyData' ->
            Ac.unifyEqualsNormalized
                tools
                term1
                term2
                unifyEqualsChildren
                normalized1
                normalized2
                acData
          where
            NormAcData{normalized1, normalized2, term1, term2, acData} = unifyData'
