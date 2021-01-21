{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

-- For instance Applicative:
{-# LANGUAGE Strict               #-}
{-# LANGUAGE UndecidableInstances #-}

module Kore.Internal.SideCondition
    ( SideCondition  -- Constructor not exported on purpose
    , fromCondition
    , fromPredicate
    , andCondition
    , assumeTrueCondition
    , assumeTruePredicate
    , mapVariables
    , top
    , topTODO
    , toPredicate
    , toRepresentation
    , replaceTerm
    , replacePredicate
    , cannotReplaceTerm
    , cannotReplacePredicate
    , assumeDefined
    , fromDefinedTerms
    , generateNormalizedAcs
    , simplifyConjunctionByAssumption
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData
    )
import qualified Control.Lens as Lens
import Control.Monad.State.Strict
    ( StateT
    , runStateT
    )
import qualified Control.Monad.State.Strict as State
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Product
    ( field
    )
import Data.HashMap.Strict
    ( HashMap
    )
import qualified Data.HashMap.Strict as HashMap
import Data.HashSet
    ( HashSet
    )
import qualified Data.HashSet as HashSet
import Data.List
    ( sortOn
    )
import Data.List.Extra
    ( nubOrdBy
    )
import qualified Data.Map.Strict as Map
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Changed
import Debug
import Kore.Attribute.Pattern.FreeVariables
    ( HasFreeVariables (..)
    )
import Kore.Attribute.Synthetic
    ( synthesize
    )
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.InternalList
    ( InternalList (..)
    )
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.NormalizedAc
    ( AcWrapper (..)
    , InternalAc (..)
    , NormalizedAc (..)
    , emptyNormalizedAc
    , getConcreteKeysOfAc
    , getSymbolicKeysOfAc
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.Predicate
    ( pattern PredicateEquals
    , pattern PredicateExists
    , pattern PredicateForall
    , pattern PredicateNot
    , makeFalsePredicate
    , makeTruePredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition.SideCondition as SideCondition
import Kore.Internal.Symbol
    ( isConstructor
    , isFunction
    )
import Kore.Internal.TermLike
    ( pattern App_
    , pattern Equals_
    , pattern Exists_
    , pattern Forall_
    , pattern Inj_
    , pattern InternalBool_
    , pattern InternalBytes_
    , pattern InternalInt_
    , pattern InternalList_
    , pattern InternalMap_
    , pattern InternalSet_
    , pattern InternalString_
    , pattern Mu_
    , pattern Nu_
    , TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.Syntax.Variable
import Kore.TopBottom
    ( TopBottom (..)
    )
import Kore.Unparser
    ( Unparse (..)
    )
import Pair
import Pretty
    ( Pretty (..)
    )
import qualified Pretty
import qualified SQL

{-| Side condition used in the evaluation context.

It contains a predicate assumed to be true, and a table of term replacements,
which is used when simplifying terms. The table is constructed from the predicate,
see 'simplifyConjunctionByAssumption'.

Warning! When simplifying a pattern, extra care should be taken that the
'SideCondition' sent to the simplifier isn't created from the same 'Condition'
which is sent to be simplified.

The predicate is usually used to remove infeasible branches, but it may also
be used for other purposes, say, to remove redundant parts of the result predicate.
-}
data SideCondition variable =
    SideCondition
        { assumedTrue
            :: !(MultiAnd (Predicate variable))
        , termReplacements
            :: !(HashMap (TermLike variable) (TermLike variable))
        , predicateReplacements
            :: !(HashMap (Predicate variable) (Predicate variable))
        , definedTerms
            :: !(HashSet (TermLike variable))
        }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance InternalVariable variable => SQL.Column (SideCondition variable) where
    defineColumn = SQL.defineTextColumn
    toColumn = SQL.toColumn . Pretty.renderText . Pretty.layoutOneLine . pretty

instance TopBottom (SideCondition variable) where
    isTop sideCondition@(SideCondition _ _ _ _) =
        isTop assumedTrue
      where
        SideCondition { assumedTrue } = sideCondition
    isBottom sideCondition@(SideCondition _ _ _ _) =
        isBottom assumedTrue
      where
        SideCondition { assumedTrue } = sideCondition

instance Ord variable => HasFreeVariables (SideCondition variable) variable
  where
    freeVariables sideCondition@(SideCondition _ _ _ _) =
        freeVariables assumedTrue
      where
        SideCondition { assumedTrue } = sideCondition

instance InternalVariable variable => Pretty (SideCondition variable) where
    pretty
        SideCondition
            { assumedTrue
            , termReplacements
            , predicateReplacements
            , definedTerms
            }
      =
        Pretty.vsep $
            [ "Assumed true condition:"
            , Pretty.indent 4 (Pretty.pretty . MultiAnd.toPredicate $ assumedTrue)
            , "Term replacements:"
            ]
            <> HashMap.foldlWithKey' (acc unparse) [] termReplacements
            <> [ "Term replacements:" ]
            <> HashMap.foldlWithKey' (acc Pretty.pretty) [] predicateReplacements
            <> [ "Assumed to be defined:" ]
            <> (unparse <$> HashSet.toList definedTerms)
      where
        acc showFunc result key value =
            result <>
            [ Pretty.indent 4 "Key:"
            , Pretty.indent 6 $ showFunc key
            , Pretty.indent 4 "Value:"
            , Pretty.indent 6 $ showFunc value
            ]

instance From (SideCondition variable) (MultiAnd (Predicate variable))
  where
    from condition@(SideCondition _ _ _ _) = assumedTrue condition
    {-# INLINE from #-}

instance InternalVariable variable =>
    From (MultiAnd (Predicate variable)) (SideCondition variable)
  where
    from multiAnd =
        -- TODO: refactor a little
        let ( assumedTrue, DoubleMap termReplacements predicateReplacements ) =
                  simplifyConjunctionByAssumption multiAnd
                  & extract
         in SideCondition
            { assumedTrue
            , termReplacements
            , predicateReplacements
            , definedTerms = mempty
            }
    {-# INLINE from #-}

instance
    InternalVariable variable
    => From (SideCondition variable) (Predicate variable)
  where
    from = toPredicate
    {-# INLINE from #-}

instance
    InternalVariable variable
    => From (Predicate variable) (SideCondition variable)
  where
    from = fromPredicate
    {-# INLINE from #-}

instance InternalVariable variable =>
    From (Condition variable) (SideCondition variable)
  where
    from = fromCondition
    {-# INLINE from #-}

instance InternalVariable variable =>
    From (SideCondition variable) (Condition variable)
  where
    from = Condition.fromPredicate . toPredicate
    {-# INLINE from #-}

top :: InternalVariable variable => SideCondition variable
top =
    SideCondition
        { assumedTrue = MultiAnd.top
        , termReplacements = mempty
        , predicateReplacements = mempty
        , definedTerms = mempty
        }

-- TODO(ana.pantilie): Should we look into removing this?
-- | A 'top' 'Condition' for refactoring which should eventually be removed.
topTODO :: InternalVariable variable => SideCondition variable
topTODO = top

{- | A 'SideCondition' and a 'Condition' are combined by assuming
their conjunction to be true, and creating a new table of replacements
from the new predicate.
 -}
andCondition
    :: InternalVariable variable
    => SideCondition variable
    -> Condition variable
    -> SideCondition variable
andCondition
    sideCondition
    (from @(Condition _) @(MultiAnd _) -> newCondition)
  =
    -- TODO: refactor a little
    let combinedConditions = oldCondition <> newCondition
        (assumedTrue, DoubleMap termReplacements predicateReplacements) =
            simplifyConjunctionByAssumption combinedConditions
            & extract
     in SideCondition
        { assumedTrue
        , termReplacements
        , predicateReplacements
        , definedTerms
        }
  where
    SideCondition { assumedTrue = oldCondition, definedTerms } = sideCondition

assumeTrueCondition
    :: InternalVariable variable
    => Condition variable
    -> SideCondition variable
assumeTrueCondition = fromCondition

assumeTruePredicate
    :: InternalVariable variable
    => Predicate variable
    -> SideCondition variable
assumeTruePredicate = fromPredicate

toPredicate
    :: InternalVariable variable
    => SideCondition variable
    -> Predicate variable
toPredicate condition@(SideCondition _ _ _ _) =
    MultiAnd.toPredicate assumedTrue
  where
    SideCondition { assumedTrue } = condition

fromPredicate
    :: InternalVariable variable
    => Predicate variable
    -> SideCondition variable
fromPredicate = from @(MultiAnd _) . MultiAnd.fromPredicate

mapVariables
    :: (InternalVariable variable1, InternalVariable variable2)
    => AdjSomeVariableName (variable1 -> variable2)
    -> SideCondition variable1
    -> SideCondition variable2
mapVariables adj condition@(SideCondition _ _ _ _) =
    let assumedTrue' =
            MultiAnd.map (Predicate.mapVariables adj) assumedTrue
        termReplacements' =
            mapKeysAndValues (TermLike.mapVariables adj) termReplacements
        predicateReplacements' =
            mapKeysAndValues (Predicate.mapVariables adj) predicateReplacements
        definedTerms' =
            HashSet.map (TermLike.mapVariables adj) definedTerms
     in SideCondition
            { assumedTrue = assumedTrue'
            , termReplacements = termReplacements'
            , predicateReplacements = predicateReplacements'
            , definedTerms = definedTerms'
            }
  where
    SideCondition
        { assumedTrue
        , termReplacements
        , predicateReplacements
        , definedTerms
        } = condition
    mapKeysAndValues f hashMap =
        HashMap.fromList
        $ Bifunctor.bimap f f
        <$> HashMap.toList hashMap

fromCondition
    :: InternalVariable variable
    => Condition variable
    -> SideCondition variable
fromCondition = fromPredicate . Condition.toPredicate

fromDefinedTerms
    :: InternalVariable variable
    => HashSet (TermLike variable)
    -> SideCondition variable
fromDefinedTerms definedTerms =
    top { definedTerms }

toRepresentation
    :: InternalVariable variable
    => SideCondition variable
    -> SideCondition.Representation
toRepresentation =
    mkRepresentation
    . mapVariables @_ @VariableName (pure toVariableName)

{- | Looks up the term in the table of replacements.
 -}
replaceTerm
    :: InternalVariable variable
    => SideCondition variable
    -> TermLike variable
    -> Maybe (TermLike variable)
replaceTerm SideCondition { termReplacements } original =
    HashMap.lookup original termReplacements

{- | Looks up the predicate in the table of replacements.
 -}
replacePredicate
    :: InternalVariable variable
    => SideCondition variable
    -> Predicate variable
    -> Maybe (Predicate variable)
replacePredicate SideCondition { predicateReplacements } original =
    HashMap.lookup original predicateReplacements

{- | If the term isn't a key in the table of replacements
then it cannot be replaced.
 -}
cannotReplaceTerm
    :: InternalVariable variable
    => SideCondition variable
    -> TermLike variable
    -> Bool
cannotReplaceTerm SideCondition { termReplacements } term =
    HashMap.lookup term termReplacements & isNothing

{- | If the predicate isn't a key in the table of replacements
then it cannot be replaced.
 -}
cannotReplacePredicate
    :: InternalVariable variable
    => SideCondition variable
    -> Predicate variable
    -> Bool
cannotReplacePredicate SideCondition { predicateReplacements } predicate =
    HashMap.lookup predicate predicateReplacements & isNothing

data DoubleMap variable = DoubleMap
    { termLikeMap :: HashMap (TermLike variable) (TermLike variable)
    , predMap :: HashMap (Predicate variable) (Predicate variable)
    }
    deriving (Eq, GHC.Generic, Show)


{- | Simplify the conjunction of 'Predicate' clauses by assuming each is true.
The conjunction is simplified by the identity:
@
A ∧ P(A) = A ∧ P(⊤)
@
 -}
simplifyConjunctionByAssumption
    :: forall variable
    .  InternalVariable variable
    => MultiAnd (Predicate variable)
    -> Changed
        ( MultiAnd (Predicate variable)
        , DoubleMap variable
        )
simplifyConjunctionByAssumption (toList -> andPredicates) =
    (fmap . Bifunctor.first) MultiAnd.make
    $ flip runStateT (DoubleMap HashMap.empty HashMap.empty)
    $ for (sortBySize andPredicates)
    $ \original -> do
        result <- applyAssumptions original
        assume result
        return result
  where
    -- Sorting by size ensures that every clause is considered before any clause
    -- which could contain it, because the containing clause is necessarily
    -- larger.
    sortBySize :: [Predicate variable] -> [Predicate variable]
    sortBySize = sortOn predSize

    size :: TermLike variable -> Int
    size =
        Recursive.fold $ \(_ :< termLikeF) ->
            case termLikeF of
                TermLike.EvaluatedF evaluated -> TermLike.getEvaluated evaluated
                TermLike.DefinedF defined -> TermLike.getDefined defined
                _ -> 1 + sum termLikeF

    predSize :: Predicate variable -> Int
    predSize =
        Recursive.fold $ \(_ :< predF) ->
            case predF of
                Predicate.CeilF ceil_ -> 1 + sum (size <$> ceil_)
                Predicate.EqualsF equals_ -> 1 + sum (size <$> equals_)
                Predicate.FloorF floor_ -> 1 + sum (size <$> floor_)
                Predicate.InF in_ -> 1 + sum (size <$> in_)
                _ -> 1 + sum predF

    assume
        :: Predicate variable ->
        StateT (DoubleMap variable) Changed ()
    assume predicate =
        State.modify' (assumeEqualTerms . assumePredicate)
      where
        assumePredicate =
            case predicate of
                PredicateNot notChild ->
                    -- Infer that the predicate is \bottom.
                    Lens.over (field @"predMap") $
                        HashMap.insert notChild makeFalsePredicate
                _ ->
                    -- Infer that the predicate is \top.
                    Lens.over (field @"predMap") $
                        HashMap.insert predicate makeTruePredicate
        assumeEqualTerms =
            case predicate of
                PredicateEquals t1 t2 ->
                    case retractLocalFunction (TermLike.mkEquals_ t1 t2) of
                        Just (Pair t1' t2') ->
                            Lens.over (field @"termLikeMap") $
                                HashMap.insert t1' t2'
                        _ -> id
                _ -> id

    applyAssumptions
        ::  Predicate variable
        ->  StateT (DoubleMap variable) Changed (Predicate variable)
    applyAssumptions replaceIn = do
        assumptions <- State.get
        lift (applyAssumptionsWorker assumptions replaceIn)

    applyAssumptionsWorker
        :: DoubleMap variable
        -> Predicate variable
        -> Changed (Predicate variable)
    applyAssumptionsWorker assumptions original
      | Just result <- HashMap.lookup original (predMap assumptions) = Changed result

      | HashMap.null (termLikeMap assumptions') &&
        HashMap.null (predMap assumptions') = Unchanged original

      | otherwise = (case replaceIn of
          Predicate.CeilF ceil_ -> Predicate.CeilF <$> traverse
            (applyAssumptionsWorkerTerm (termLikeMap assumptions')) ceil_
          Predicate.FloorF floor_ -> Predicate.FloorF <$> traverse
            (applyAssumptionsWorkerTerm (termLikeMap assumptions')) floor_
          Predicate.EqualsF equals_ -> Predicate.EqualsF <$> traverse
            (applyAssumptionsWorkerTerm (termLikeMap assumptions')) equals_
          Predicate.InF in_ -> Predicate.InF <$> traverse
            (applyAssumptionsWorkerTerm (termLikeMap assumptions')) in_
          _ -> traverse (applyAssumptionsWorker assumptions') replaceIn
        )
        & getChanged
        -- The next line ensures that if the result is Unchanged, any allocation
        -- performed while computing that result is collected.
        & maybe (Unchanged original) (Changed . synthesize)

      where
        _ :< replaceIn = Recursive.project original

        assumptions'
          | PredicateExists var _ <- original = restrictAssumptions (inject var)
          | PredicateForall var _ <- original = restrictAssumptions (inject var)
          | otherwise = assumptions

        restrictAssumptions Variable { variableName } =
            Lens.over (field @"termLikeMap")
            (HashMap.filterWithKey (\term _ -> wouldNotCaptureTerm term))
            $
            Lens.over (field @"predMap")
            (HashMap.filterWithKey (\predicate _ -> wouldNotCapture predicate))
            assumptions
          where
            wouldNotCapture = not . Predicate.hasFreeVariable variableName
            wouldNotCaptureTerm = not . TermLike.hasFreeVariable variableName

    applyAssumptionsWorkerTerm
        :: HashMap (TermLike variable) (TermLike variable)
        -> TermLike variable
        -> Changed (TermLike variable)
    applyAssumptionsWorkerTerm assumptions original
      | Just result <- HashMap.lookup original assumptions = Changed result

      | HashMap.null assumptions' = Unchanged original

      | otherwise =
        traverse (applyAssumptionsWorkerTerm assumptions') replaceIn
        & getChanged
        -- The next line ensures that if the result is Unchanged, any allocation
        -- performed while computing that result is collected.
        & maybe (Unchanged original) (Changed . synthesize)

      where
        _ :< replaceIn = Recursive.project original

        assumptions'
          | Exists_ _ var _ <- original = restrictAssumptions (inject var)
          | Forall_ _ var _ <- original = restrictAssumptions (inject var)
          | Mu_       var _ <- original = restrictAssumptions (inject var)
          | Nu_       var _ <- original = restrictAssumptions (inject var)
          | otherwise = assumptions

        restrictAssumptions Variable { variableName } =
            HashMap.filterWithKey
                (\termLike _ -> wouldNotCapture termLike)
                assumptions
          where
            wouldNotCapture = not . TermLike.hasFreeVariable variableName

{- | Get a local function definition from a 'TermLike'.
A local function definition is a predicate that we can use to evaluate a
function locally (based on the side conditions) when none of the functions
global definitions (axioms) apply. We are looking for a 'TermLike' of the form
@
\equals(f(...), C(...))
@
where @f@ is a function and @C@ is a constructor, sort injection or builtin.
@retractLocalFunction@ will match an @\equals@ predicate with its arguments
in either order, but the function pattern is always returned first in the
'Pair'.
 -}
retractLocalFunction
    :: TermLike variable
    -> Maybe (Pair (TermLike variable))
retractLocalFunction =
    \case
        Equals_ _ _ term1 term2 -> go term1 term2 <|> go term2 term1
        _ -> Nothing
  where
    go term1@(App_ symbol1 _) term2
      | isFunction symbol1 =
        -- TODO (thomas.tuegel): Add tests.
        case term2 of
            App_ symbol2 _
              | isConstructor symbol2 -> Just (Pair term1 term2)
            Inj_ _     -> Just (Pair term1 term2)
            InternalInt_ _ -> Just (Pair term1 term2)
            InternalBytes_ _ _ -> Just (Pair term1 term2)
            InternalString_ _ -> Just (Pair term1 term2)
            InternalBool_ _ -> Just (Pair term1 term2)
            InternalList_ _ -> Just (Pair term1 term2)
            InternalMap_ _ -> Just (Pair term1 term2)
            InternalSet_ _ -> Just (Pair term1 term2)
            _          -> Nothing
    go _ _ = Nothing

assumeDefined
    :: forall variable
    .  InternalVariable variable
    => TermLike variable
    -> SideCondition variable
assumeDefined term =
    assumeDefinedWorker term
    & fromDefinedTerms
  where
    assumeDefinedWorker
        :: TermLike variable
        -> HashSet (TermLike variable)
    assumeDefinedWorker term' =
        case term' of
            TermLike.And_ _ child1 child2 ->
                let result1 = assumeDefinedWorker child1
                    result2 = assumeDefinedWorker child2
                 in asSet term' <> result1 <> result2
            TermLike.App_ _ children ->
                asSet term' <> foldMap assumeDefinedWorker children
            TermLike.Ceil_ _ _ child ->
                asSet term' <> assumeDefinedWorker child
            TermLike.InternalList_ internalList ->
                asSet term'
                <> foldMap assumeDefinedWorker (internalListChild internalList)
            TermLike.InternalMap_ internalMap ->
                let definedElems =
                        getDefinedElementsOfAc internalMap
                    definedMaps =
                        generateNormalizedAcs internalMap
                        & HashSet.map TermLike.mkInternalMap
                 in foldMap assumeDefinedWorker definedElems
                    <> asSet term'
                    <> definedMaps
            TermLike.InternalSet_ internalSet ->
                let definedElems =
                        getDefinedElementsOfAc internalSet
                    definedSets =
                        generateNormalizedAcs internalSet
                        & HashSet.map TermLike.mkInternalSet
                 in foldMap assumeDefinedWorker definedElems
                    <> asSet term'
                    <> definedSets
            TermLike.Forall_ _ _ child ->
                asSet term' <> assumeDefinedWorker child
            TermLike.In_ _ _ child1 child2 ->
                let result1 = assumeDefinedWorker child1
                    result2 = assumeDefinedWorker child2
                 in asSet term' <> result1 <> result2
            TermLike.Bottom_ _ ->
                error
                    "Internal error: cannot assume\
                    \ a \\bottom pattern is defined."
            _ -> asSet term'
    asSet newTerm
      | TermLike.isDefinedPattern newTerm = mempty
      | otherwise = HashSet.singleton newTerm

    getDefinedElementsOfAc
        :: forall normalized
        .  AcWrapper normalized
        => InternalAc (TermLike Concrete) normalized (TermLike variable)
        -> HashSet (TermLike variable)
    getDefinedElementsOfAc (builtinAcChild -> normalizedAc) =
        let symbolicKeys = getSymbolicKeysOfAc normalizedAc
            concreteKeys =
                getConcreteKeysOfAc normalizedAc
                & fmap TermLike.fromConcrete
            opaqueElems = opaque (unwrapAc normalizedAc)
         in HashSet.fromList symbolicKeys
            <> HashSet.fromList concreteKeys
            <> HashSet.fromList opaqueElems

-- | Generates the minimal set of defined collections from which
-- definedness of any sub collection can be inferred. The resulting
-- set will not contain the input collection itself.
generateNormalizedAcs
    :: forall normalized variable
    .  InternalVariable variable
    => Ord (Element normalized (TermLike variable))
    => Ord (Value normalized (TermLike variable))
    => Ord (normalized (TermLike Concrete) (TermLike variable))
    => Hashable (normalized (TermLike Concrete) (TermLike variable))
    => AcWrapper normalized
    => InternalAc (TermLike Concrete) normalized (TermLike variable)
    -> HashSet (InternalAc (TermLike Concrete) normalized (TermLike variable))
generateNormalizedAcs internalAc
  | numberOfElements <= 2 = mempty
  | otherwise =
    let symbolicPairs =
            [(x,y) | x <- symbolicElems, y <- symbolicElems , x /= y]
            & nubOrdBy applyComm
        concretePairs =
            [(x,y) | x <- concreteElems, y <- concreteElems, x /= y]
            & nubOrdBy applyComm
        opaquePairs =
            [(x,y) | x <- opaqueElems, y <- opaqueElems, x /= y]
            & nubOrdBy applyComm
        symbolicConcrete =
            (,) <$> symbolicElems <*> concreteElems
        symbolicOpaque =
            (,) <$> symbolicElems <*> opaqueElems
        concreteOpaque =
            (,) <$> concreteElems <*> opaqueElems
     in HashSet.fromList (symbolicToAc <$> symbolicPairs)
        <> HashSet.fromList (concreteToAc <$> concretePairs)
        <> HashSet.fromList (opaqueToAc <$> opaquePairs)
        <> HashSet.fromList (symbolicConcreteToAc <$> symbolicConcrete)
        <> HashSet.fromList (symbolicOpaqueToAc <$> symbolicOpaque)
        <> HashSet.fromList (concreteOpaqueToAc <$> concreteOpaque)
  where
    InternalAc
        { builtinAcChild
        , builtinAcSort
        , builtinAcUnit
        , builtinAcConcat
        , builtinAcElement
        } = internalAc
    numberOfElements =
        length symbolicElems
        + length concreteElems
        + length opaqueElems
    symbolicElems = elementsWithVariables . unwrapAc $ builtinAcChild
    concreteElems = Map.toList . concreteElements . unwrapAc $ builtinAcChild
    opaqueElems = opaque . unwrapAc $ builtinAcChild
    applyComm p1 p2
      | p1 == p2 = EQ
      | swap p1 == p2 = EQ
      | otherwise = compare p1 p2
    symbolicToAc (symbolic1, symbolic2) =
        let symbolicAc =
                emptyNormalizedAc
                    { elementsWithVariables = [symbolic1, symbolic2]
                    }
                & wrapAc
         in toInternalAc symbolicAc
    concreteToAc (concrete1, concrete2) =
        let concreteAc =
                emptyNormalizedAc
                    { concreteElements = [concrete1, concrete2] & Map.fromList
                    }
                & wrapAc
         in toInternalAc concreteAc
    opaqueToAc (opaque1, opaque2) =
        let opaqueAc =
                emptyNormalizedAc
                    { opaque = [opaque1, opaque2]
                    }
                & wrapAc
         in toInternalAc opaqueAc
    symbolicConcreteToAc (symbolic, concrete) =
        let symbolicConcreteAc =
                emptyNormalizedAc
                    { elementsWithVariables = [symbolic]
                    , concreteElements = [concrete] & Map.fromList
                    }
                & wrapAc
         in toInternalAc symbolicConcreteAc
    symbolicOpaqueToAc (symbolic, opaque') =
        let symbolicOpaqueAc =
                emptyNormalizedAc
                    { elementsWithVariables = [symbolic]
                    , opaque = [opaque']
                    }
                & wrapAc
         in toInternalAc symbolicOpaqueAc
    concreteOpaqueToAc (concrete, opaque') =
        let concreteOpaqueAc =
                emptyNormalizedAc
                    { concreteElements = [concrete] & Map.fromList
                    , opaque = [opaque']
                    }
                & wrapAc
         in toInternalAc concreteOpaqueAc
    toInternalAc normalized =
         InternalAc
             { builtinAcChild = normalized
             , builtinAcUnit
             , builtinAcElement
             , builtinAcSort
             , builtinAcConcat
             }
