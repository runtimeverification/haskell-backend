{- |
Module      : Kore.Builtin.Set
Description : Built-in sets
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : thomas.tuegel@runtimeverification.com

This module is intended to be imported qualified, to avoid collision with other
builtin modules.

@
    import qualified Kore.Builtin.Set as Set
@
 -}
module Kore.Builtin.Set
    ( sort
    , assertSort
    , sortDeclVerifiers
    , isSetSort
    , symbolVerifiers
    , builtinFunctions
    , Domain.Builtin
    , returnConcreteSet
    , Set.asTermLike
    , internalize
    , expectBuiltinSet
    , expectConcreteBuiltinSet
      -- * Unification
    , unifyEquals
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Control.Error
    ( MaybeT (MaybeT)
    , fromMaybe
    , hoistMaybe
    , runMaybeT
    )
import qualified Control.Monad as Monad
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
    ( toList
    )
import qualified Data.HashMap.Strict as HashMap
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import qualified Kore.Attribute.Symbol as Attribute
    ( Symbol
    )
import qualified Kore.Builtin.AssociativeCommutative as Ac
import Kore.Builtin.Attributes
    ( isConstructorModulo_
    )
import qualified Kore.Builtin.Bool as Bool
import Kore.Builtin.Builtin
    ( acceptAnySort
    )
import qualified Kore.Builtin.Builtin as Builtin
import qualified Kore.Builtin.Int as Int
import qualified Kore.Builtin.List as List
import qualified Kore.Builtin.Set.Set as Set
import qualified Kore.Domain.Builtin as Domain
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
    ( pattern App_
    , pattern Builtin_
    , Concrete
    , InternalVariable
    , TermLike
    , mkSort
    , termLikeSort
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Sort
    ( Sort
    )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Syntax.Sentence
    ( SentenceSort (SentenceSort)
    )
import qualified Kore.Syntax.Sentence as Sentence.DoNotUse
    ( SentenceSort (..)
    )
import Kore.Unification.Unify
    ( MonadUnify
    )
import qualified Kore.Unification.Unify as Monad.Unify

{- | Builtin name of the @Set@ sort.
 -}
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
        SentenceSort { sentenceSortName } = sentenceSort
        expectedSort = mkSort sentenceSortName

{- | Verify that hooked symbol declarations are well-formed.

  See also: 'Builtin.verifySymbol'

 -}
symbolVerifiers :: Builtin.SymbolVerifiers
symbolVerifiers =
    HashMap.fromList
    [ ( Set.concatKey
      , Builtin.verifySymbol assertSort [assertSort , assertSort]
      )
    , ( Set.elementKey
      , Builtin.verifySymbol assertSort [acceptAnySort]
      )
    , ( Set.unitKey
      , Builtin.verifySymbol assertSort []
      )
    , ( Set.inKey
      , Builtin.verifySymbol Bool.assertSort [acceptAnySort, assertSort]
      )
    , ( Set.differenceKey
      , Builtin.verifySymbol assertSort [assertSort, assertSort]
      )
    , ( Set.toListKey
      , Builtin.verifySymbol List.assertSort [assertSort]
      )
    , ( Set.sizeKey
      , Builtin.verifySymbol Int.assertSort [assertSort]
      )
    , ( Set.intersectionKey
      , Builtin.verifySymbol assertSort [assertSort, assertSort]
      )
    , ( Set.list2setKey
      , Builtin.verifySymbol assertSort [List.assertSort]
      )
    ]

{- | Returns @empty@ if the argument is not a @NormalizedSet@ domain value.

Returns the @NormalizedSet@ otherwise.
-}
expectBuiltinSet
    :: MonadSimplify m
    => Text  -- ^ Context for error message
    -> TermLike variable  -- ^ Operand pattern
    -> MaybeT m (Ac.TermNormalizedAc Domain.NormalizedSet variable)
expectBuiltinSet ctx set =
    case set of
        Builtin_ domain ->
            case domain of
                Domain.BuiltinSet Domain.InternalAc { builtinAcChild } ->
                    return builtinAcChild
                _ ->
                    Builtin.verifierBug
                    $ Text.unpack ctx ++ ": Domain value is not a set"
        _ -> empty

{- | Returns @empty@ if the argument is not a @NormalizedSet@ domain value
which consists only of concrete elements.

Returns the @Set@ of concrete elements otherwise.
-}
expectConcreteBuiltinSet
    :: MonadSimplify m
    => Text  -- ^ Context for error message
    -> TermLike variable  -- ^ Operand pattern
    -> MaybeT m (Map (TermLike Concrete) (Domain.SetValue (TermLike variable)))
expectConcreteBuiltinSet ctx _set = do
    _set <- expectBuiltinSet ctx _set
    case Domain.unwrapAc _set of
        Domain.NormalizedAc
            { elementsWithVariables = []
            , concreteElements
            , opaque = []
            } -> return concreteElements
        _ -> empty

{- | Converts a @Set@ of concrete elements to a @NormalizedSet@ and returns it
as a function result.
-}
returnConcreteSet
    :: (MonadSimplify m, InternalVariable variable)
    => Sort
    -> Map (TermLike Concrete) (Domain.SetValue (TermLike variable))
    -> m (AttemptedAxiom variable)
returnConcreteSet = Ac.returnConcreteAc

evalElement :: Builtin.Function
evalElement =
    Builtin.functionEvaluator evalElement0
  where
    evalElement0 _ resultSort arguments =
        Builtin.getAttemptedAxiom
            (case arguments of
                [_elem] ->
                    case TermLike.asConcrete _elem of
                        Just concrete ->
                            returnConcreteSet
                                resultSort
                                (Map.singleton concrete Domain.SetValue)
                        Nothing ->
                            Ac.returnAc resultSort
                            $ Domain.wrapAc Domain.NormalizedAc
                                { elementsWithVariables =
                                    [Domain.SetElement _elem]
                                , concreteElements = Map.empty
                                , opaque = []
                                }
                _ -> Builtin.wrongArity Set.elementKey
            )

evalIn :: Builtin.Function
evalIn =
    Builtin.functionEvaluator evalIn0
  where
    evalIn0 :: Builtin.FunctionImplementation
    evalIn0 _ resultSort = \arguments ->
        Builtin.getAttemptedAxiom $ do
            let (_elem, _set) =
                    case arguments of
                        [_elem, _set] -> (_elem, _set)
                        _ -> Builtin.wrongArity Set.inKey
            _elem <- hoistMaybe $ Builtin.toKey _elem
            _set <- expectConcreteBuiltinSet Set.inKey _set
            (Builtin.appliedFunction . asExpandedBoolPattern)
                (Map.member _elem _set)
      where
        asExpandedBoolPattern = Bool.asPattern resultSort

evalUnit :: Builtin.Function
evalUnit =
    Builtin.functionEvaluator evalUnit0
  where
    evalUnit0 _ resultSort =
        \case
            [] -> returnConcreteSet resultSort Map.empty
            _ -> Builtin.wrongArity Set.unitKey

evalConcat :: Builtin.Function
evalConcat =
    Builtin.functionEvaluator evalConcat0
  where
    evalConcat0
        :: forall variable m
        .  InternalVariable variable
        => MonadSimplify m
        => TermLikeSimplifier
        -> Sort
        -> [TermLike variable]
        -> m (AttemptedAxiom variable)
    evalConcat0 _ resultSort arguments = Builtin.getAttemptedAxiom $ do
        let (_set1, _set2) =
                case arguments of
                    [_set1, _set2] -> (_set1, _set2)
                    _ -> Builtin.wrongArity Set.concatKey

            normalized1 :: Ac.NormalizedOrBottom Domain.NormalizedSet variable
            normalized1 = Ac.toNormalized _set1
            normalized2 :: Ac.NormalizedOrBottom Domain.NormalizedSet variable
            normalized2 = Ac.toNormalized _set2

        Ac.evalConcatNormalizedOrBottom resultSort normalized1 normalized2

evalDifference :: Builtin.Function
evalDifference =
    Builtin.functionEvaluator evalDifference0
  where
    ctx = Set.differenceKey
    evalDifference0 :: Builtin.FunctionImplementation
    evalDifference0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let (_set1, _set2) =
                    case arguments of
                        [_set1, _set2] -> (_set1, _set2)
                        _ -> Builtin.wrongArity Set.differenceKey
                rightIdentity = do
                    _set2 <- expectConcreteBuiltinSet ctx _set2
                    if Map.null _set2
                        then
                            Builtin.appliedFunction
                            $ Pattern.fromTermLike _set1
                        else empty
                bothConcrete = do
                    _set1 <- expectConcreteBuiltinSet ctx _set1
                    _set2 <- expectConcreteBuiltinSet ctx _set2
                    returnConcreteSet resultSort (Map.difference _set1 _set2)
            rightIdentity <|> bothConcrete

evalToList :: Builtin.Function
evalToList = Builtin.functionEvaluator evalToList0
  where
    evalToList0 :: Builtin.FunctionImplementation
    evalToList0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let _set =
                        case arguments of
                            [_set] -> _set
                            _      -> Builtin.wrongArity Set.toListKey
            _set <- expectConcreteBuiltinSet Set.toListKey _set
            List.returnList resultSort
                . fmap TermLike.fromConcrete
                . Seq.fromList
                . map dropNoValue
                . Map.toList
                $ _set

    dropNoValue (a, Domain.SetValue) = a

evalSize :: Builtin.Function
evalSize = Builtin.functionEvaluator evalSize0
  where
    evalSize0 :: Builtin.FunctionImplementation
    evalSize0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let _set =
                        case arguments of
                            [_set] -> _set
                            _      -> Builtin.wrongArity Set.sizeKey
            _set <- expectConcreteBuiltinSet Set.sizeKey _set
            Builtin.appliedFunction
                . Int.asPattern resultSort
                . toInteger
                . Map.size
                $ _set

evalIntersection :: Builtin.Function
evalIntersection =
    Builtin.functionEvaluator evalIntersection0
  where
    ctx = Set.intersectionKey
    evalIntersection0 :: Builtin.FunctionImplementation
    evalIntersection0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let (_set1, _set2) =
                    case arguments of
                        [_set1, _set2] -> (_set1, _set2)
                        _ -> Builtin.wrongArity Set.intersectionKey
            _set1 <- expectConcreteBuiltinSet ctx _set1
            _set2 <- expectConcreteBuiltinSet ctx _set2
            returnConcreteSet resultSort (Map.intersection _set1 _set2)

evalList2set :: Builtin.Function
evalList2set =
    Builtin.functionEvaluator evalList2set0
  where
    evalList2set0 :: Builtin.FunctionImplementation
    evalList2set0 _ resultSort arguments =
        Builtin.getAttemptedAxiom $ do
            let _list =
                    case arguments of
                        [_map] -> _map
                        _      -> Builtin.wrongArity Set.list2setKey
            _list <- List.expectConcreteBuiltinList Set.list2setKey _list
            let _set = Map.fromList
                            $ fmap (\x -> (x, Domain.SetValue))
                            $ Foldable.toList _list
            returnConcreteSet resultSort _set

{- | Implement builtin function evaluation.
 -}
builtinFunctions :: Map Text Builtin.Function
builtinFunctions =
    Map.fromList
        [ (Set.concatKey, evalConcat)
        , (Set.elementKey, evalElement)
        , (Set.unitKey, evalUnit)
        , (Set.inKey, evalIn)
        , (Set.differenceKey, evalDifference)
        , (Set.toListKey, evalToList)
        , (Set.sizeKey, evalSize)
        , (Set.intersectionKey, evalIntersection)
        , (Set.list2setKey, evalList2set)
        ]

{- | Convert a Set-sorted 'TermLike' to its internal representation.

The 'TermLike' is unmodified if it is not Set-sorted. @internalize@ only
operates at the top-most level, it does not descend into the 'TermLike' to
internalize subterms.

 -}
internalize
    :: InternalVariable variable
    => SmtMetadataTools Attribute.Symbol
    -> TermLike variable
    -> TermLike variable
internalize tools termLike
  | fromMaybe False (isSetSort tools sort')
  -- Ac.toNormalized is greedy about 'normalizing' opaque terms, we should only
  -- apply it if we know the term head is a constructor-like symbol.
  , App_ symbol _ <- termLike
  , isConstructorModulo_ symbol =
    case Ac.toNormalized @Domain.NormalizedSet termLike of
        Ac.Bottom                    -> TermLike.mkBottom sort'
        Ac.Normalized termNormalized
          | let unwrapped = Domain.unwrapAc termNormalized
          , null (Domain.elementsWithVariables unwrapped)
          , null (Domain.concreteElements unwrapped)
          , [singleOpaqueTerm] <- Domain.opaque unwrapped
          ->
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
unifyEquals
    :: forall variable unifier
    .  (SimplifierVariable variable, MonadUnify unifier)
    => (TermLike variable -> TermLike variable -> unifier (Pattern variable))
    -> TermLike variable
    -> TermLike variable
    -> MaybeT unifier (Pattern variable)
unifyEquals
    unifyEqualsChildren
    first
    second
  = do
    tools <- Simplifier.askMetadataTools
    (Monad.guard . fromMaybe False) (isSetSort tools sort1)
    MaybeT $ do
        unifiers <- Monad.Unify.gather (runMaybeT (unifyEquals0 first second))
        case sequence unifiers of
            Nothing -> return Nothing
            Just us -> Monad.Unify.scatter (map Just us)
  where
    sort1 = termLikeSort first

    -- | Unify the two argument patterns.
    unifyEquals0
        :: TermLike variable
        -> TermLike variable
        -> MaybeT unifier (Pattern variable)
    unifyEquals0
        (Builtin_ (Domain.BuiltinSet normalized1))
        (Builtin_ (Domain.BuiltinSet normalized2))
      = do
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
        asDomain
            :: TermLike variable
            -> MaybeT unifier (TermLike variable)
        asDomain patt =
            case normalizedOrBottom of
                Ac.Normalized normalized -> do
                    tools <- Simplifier.askMetadataTools
                    return (Ac.asInternal tools sort1 normalized)
                Ac.Bottom ->
                    Monad.Trans.lift $ Monad.Unify.explainAndReturnBottom
                        "Duplicated elements in normalization."
                        first
                        second
          where
            normalizedOrBottom
                :: Ac.NormalizedOrBottom Domain.NormalizedSet variable
            normalizedOrBottom = Ac.toNormalized patt
