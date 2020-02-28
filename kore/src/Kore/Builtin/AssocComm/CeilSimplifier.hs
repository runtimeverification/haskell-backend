{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Builtin.AssocComm.CeilSimplifier
    ( newCeilSimplifier
    ) where

import Prelude.Kore

import Control.Monad
    ( zipWithM
    )
import Control.Monad.Reader
    ( ReaderT (..)
    )
import qualified Data.Foldable as Foldable
import qualified Data.Map.Strict as Map

import qualified Data.List as List
import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.OrCondition
    ( OrCondition
    )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.Predicate
    ( makeCeilPredicate_
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Internal.TermLike
    ( Ceil (..)
    , Concrete
    , InternalVariable
    , Sort
    , TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Step.Simplification.AndPredicates as And
import Kore.Step.Simplification.CeilSimplifier
import qualified Kore.Step.Simplification.Equals as Equals
import qualified Kore.Step.Simplification.Not as Not
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    )

type BuiltinAssocComm normalized variable =
    Domain.InternalAc (TermLike Concrete) normalized (TermLike variable)

type MkBuiltinAssocComm normalized variable =
    BuiltinAssocComm normalized variable -> TermLike variable

newCeilSimplifier
    ::  forall normalized variable simplifier
    .   Domain.AcWrapper normalized
    =>  Traversable (Domain.Value normalized)
    =>  InternalVariable variable
    =>  MonadSimplify simplifier
    =>  MkBuiltinAssocComm normalized variable
    ->  CeilSimplifier
            (ReaderT (SideCondition variable) simplifier)
            (TermLike variable)
            (OrCondition variable)
    ->  CeilSimplifier
            (ReaderT (SideCondition variable) simplifier)
            (BuiltinAssocComm normalized variable)
            (OrCondition variable)
newCeilSimplifier mkBuiltin ceilSimplifierTermLike =
    CeilSimplifier $ \ceil@Ceil { ceilChild } ->
    ReaderT $ \sideCondition ->
        makeEvaluateBuiltinAssocComm
            mkBuiltin
            ceilSimplifierTermLike
            sideCondition
            ceil { ceilChild = () }
            ceilChild

makeEvaluateBuiltinAssocComm
    :: forall normalized variable simplifier
    .   InternalVariable variable
    =>  MonadSimplify simplifier
    =>  Traversable (Domain.Value normalized)
    =>  Domain.AcWrapper normalized
    =>  MkBuiltinAssocComm normalized variable
    ->  CeilSimplifier
            (ReaderT (SideCondition variable) simplifier)
            (TermLike variable)
            (OrCondition variable)
    ->  SideCondition variable
    ->  Ceil Sort ()
    ->  BuiltinAssocComm normalized variable
    ->  simplifier (OrCondition variable)
makeEvaluateBuiltinAssocComm
    mkBuiltin
    ceilSimplifierTermLike
    sideCondition
    Ceil { ceilResultSort }
    internalAc@Domain.InternalAc{ builtinAcChild }
  =
    TermLike.assertConstructorLikeKeys concreteKeys $ do
        -- concreteKeys are defined by assumption
        definedKeys <- traverse defineAbstractKey abstractKeys
        definedOpaque <- traverse defineOpaque opaque
        definedValues <- traverse defineValue allValues
        -- concreteKeys are distinct by assumption
        distinctConcreteKeys <-
            traverse (flip distinctKey concreteKeys) abstractKeys
        distinctAbstractKeys <-
            zipWithM distinctKey
                abstractKeys
                (tail $ List.tails abstractKeys)
        let conditions :: MultiAnd (OrCondition variable)
            conditions =
                mconcat
                    [ MultiAnd.make definedKeys
                    , MultiAnd.make definedOpaque
                    , mconcat definedValues
                    , mconcat distinctConcreteKeys
                    , mconcat distinctAbstractKeys
                    , definedConcreteOpaquePairs
                    , definedAbstractOpaquePairs
                    , definedOpaquePairs
                    ]

        And.simplifyEvaluatedMultiPredicate sideCondition conditions
  where
    normalizedAc = Domain.unwrapAc builtinAcChild
    Domain.NormalizedAc
        { elementsWithVariables = abstractElements
        , concreteElements
        , opaque
        }
      = normalizedAc

    makeEvaluateTerm, defineAbstractKey, defineOpaque
        :: TermLike variable -> simplifier (OrCondition variable)

    makeEvaluateTerm termLike =
        runCeilSimplifierWith ceilSimplifierTermLike sideCondition
            Ceil
                { ceilResultSort
                , ceilOperandSort = TermLike.termLikeSort termLike
                , ceilChild = termLike
                }
    defineAbstractKey = makeEvaluateTerm
    defineOpaque = makeEvaluateTerm

    abstractKeys, concreteKeys :: [TermLike variable]
    abstractValues, concreteValues, allValues
        :: [Domain.Value normalized (TermLike variable)]
    (abstractKeys, abstractValues) =
        unzip (Domain.unwrapElement <$> abstractElements)
    concreteKeys = TermLike.fromConcrete <$> Map.keys concreteElements
    concreteValues = Map.elems concreteElements
    allValues = concreteValues <> abstractValues

    defineValue
        :: Domain.Value normalized (TermLike variable)
        -> simplifier (MultiAnd (OrCondition variable))
    defineValue =
        Foldable.foldlM worker mempty
      where
        worker multiAnd termLike = do
            evaluated <- makeEvaluateTerm termLike
            return (multiAnd <> MultiAnd.singleton evaluated)

    distinctKey
        :: TermLike variable
        -> [TermLike variable]
        -> simplifier (MultiAnd (OrCondition variable))
    distinctKey thisKey otherKeys =
        MultiAnd.make <$> traverse (notEquals thisKey) otherKeys

    notEquals t1 t2 =
        Equals.makeEvaluateTermsToPredicate tMin tMax sideCondition
        >>= Not.simplifyEvaluatedPredicate
      where
        -- Stabilize the order of terms under Equals.
        (tMin, tMax) = minMax t1 t2

    definedConcreteOpaquePairs =
        foldMap defineConcreteOpaque $ Map.toList concreteElements
    definedAbstractOpaquePairs =
        foldMap defineAbstractOpaque abstractElements

    defineConcreteOpaque
        :: (TermLike Concrete, Domain.Value normalized (TermLike variable))
        -> MultiAnd (OrCondition variable)
    defineConcreteOpaque elt =
        foldMap (defineConcreteOpaquePair elt) opaque

    defineConcreteOpaquePair
        :: (TermLike Concrete, Domain.Value normalized (TermLike variable))
        -> TermLike variable
        -> MultiAnd (OrCondition variable)
    defineConcreteOpaquePair (key, value) opaque1 =
        internalAc
            { Domain.builtinAcChild =
                Domain.wrapAc Domain.NormalizedAc
                    { elementsWithVariables = mempty
                    , concreteElements = Map.singleton key value
                    , opaque = [opaque1]
                    }
            }
        & mkBuiltin
        & makeSimplified
        & MultiAnd.singleton

    defineAbstractOpaque
        :: Domain.Element normalized (TermLike variable)
        -> MultiAnd (OrCondition variable)
    defineAbstractOpaque elt =
        foldMap (defineAbstractOpaquePair elt) opaque

    defineAbstractOpaquePair
        :: Domain.Element normalized (TermLike variable)
        -> TermLike variable
        -> MultiAnd (OrCondition variable)
    defineAbstractOpaquePair elt opaque1 =
        internalAc
            { Domain.builtinAcChild =
                Domain.wrapAc Domain.NormalizedAc
                    { elementsWithVariables = [elt]
                    , concreteElements = mempty
                    , opaque = [opaque1]
                    }
            }
        & mkBuiltin
        & makeSimplified
        & MultiAnd.singleton

    definedOpaquePairs :: MultiAnd (OrCondition variable)
    definedOpaquePairs =
        mconcat $ zipWith defineOpaquePairs opaque (tail $ List.tails opaque)

    defineOpaquePairs
        :: TermLike variable
        -> [TermLike variable]
        -> MultiAnd (OrCondition variable)
    defineOpaquePairs this others =
        foldMap (defineOpaquePair this) others

    defineOpaquePair
        :: TermLike variable
        -> TermLike variable
        -> MultiAnd (OrCondition variable)
    defineOpaquePair opaque1 opaque2 =
        internalAc
            { Domain.builtinAcChild =
                Domain.wrapAc Domain.NormalizedAc
                    { elementsWithVariables = mempty
                    , concreteElements = mempty
                    , opaque = [opaque1, opaque2]
                    }
            }
        & mkBuiltin
        & makeSimplified
        & MultiAnd.singleton

    makeSimplified =
        OrCondition.fromPredicate
        . Predicate.markSimplifiedMaybeConditional Nothing
        . makeCeilPredicate_
