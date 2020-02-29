{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Builtin.AssocComm.CeilSimplifier
    ( newSetCeilSimplifier
    , newMapCeilSimplifier
    , newCeilSimplifier
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Control.Monad
    ( zipWithM
    )
import Control.Monad.Reader
    ( ReaderT (..)
    )
import qualified Data.Foldable as Foldable
import qualified Data.Map.Strict as Map

import qualified Data.List as List
import qualified Kore.Builtin.Builtin as Builtin
import Kore.Domain.Builtin
    ( AcWrapper
    , Element
    , NormalizedAc (..)
    , emptyNormalizedAc
    )
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
    ( Predicate
    , makeCeilPredicate_
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

type MkNotMember normalized variable =
        Element normalized (TermLike variable)
    ->  TermLike variable
    ->  Predicate variable

newSetCeilSimplifier
    ::  forall variable simplifier
    .   InternalVariable variable
    =>  MonadSimplify simplifier
    =>  CeilSimplifier
            (ReaderT (SideCondition variable) simplifier)
            (TermLike variable)
            (OrCondition variable)
    ->  CeilSimplifier
            (ReaderT (SideCondition variable) simplifier)
            (BuiltinAssocComm Domain.NormalizedSet variable)
            (OrCondition variable)
newSetCeilSimplifier ceilSimplifierTermLike =
    CeilSimplifier $ \ceil@Ceil { ceilChild } ->
    ReaderT $ \sideCondition -> do
        let mkInternalAc normalizedAc =
                ceilChild { Domain.builtinAcChild = Domain.wrapAc normalizedAc }
            mkNotMember element termLike =
                mkInternalAc (fromElement element) { opaque = [termLike] }
                & TermLike.mkBuiltinSet
                & makeCeilPredicate_
        makeEvaluateBuiltinAssocComm
            TermLike.mkBuiltinSet
            mkNotMember
            ceilSimplifierTermLike
            sideCondition
            ceil { ceilChild = () }
            ceilChild

newMapCeilSimplifier
    ::  forall variable simplifier
    .   InternalVariable variable
    =>  MonadSimplify simplifier
    =>  CeilSimplifier
            (ReaderT (SideCondition variable) simplifier)
            (TermLike variable)
            (OrCondition variable)
    ->  CeilSimplifier
            (ReaderT (SideCondition variable) simplifier)
            (BuiltinAssocComm Domain.NormalizedMap variable)
            (OrCondition variable)
newMapCeilSimplifier ceilSimplifierTermLike =
    CeilSimplifier $ \ceil@Ceil { ceilChild } ->
    ReaderT $ \sideCondition -> do
        let mkInternalAc normalizedAc =
                ceilChild { Domain.builtinAcChild = Domain.wrapAc normalizedAc }
            mkNotMember element termLike =
                mkInternalAc (fromElement element) { opaque = [termLike] }
                & TermLike.mkBuiltinMap
                & makeCeilPredicate_
        makeEvaluateBuiltinAssocComm
            TermLike.mkBuiltinMap
            mkNotMember
            ceilSimplifierTermLike
            sideCondition
            ceil { ceilChild = () }
            ceilChild

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
    ReaderT $ \sideCondition -> do
        let mkInternalAc normalizedAc =
                ceilChild { Domain.builtinAcChild = Domain.wrapAc normalizedAc }
            mkNotMember element termLike =
                mkInternalAc (fromElement element) { opaque = [termLike] }
                & mkBuiltin
                & makeCeilPredicate_
        makeEvaluateBuiltinAssocComm
            mkBuiltin
            mkNotMember
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
    ->  MkNotMember normalized variable
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
    mkNotMember
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
                    , Foldable.foldMap notMembers opaque
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

    notMember
        :: TermLike variable
        -> Domain.Element normalized (TermLike variable)
        -> MultiAnd (OrCondition variable)
    notMember termLike element =
        mkNotMember element termLike
        & makeSimplifiedPredicate
        & MultiAnd.singleton

    notMembers :: TermLike variable -> MultiAnd (OrCondition variable)
    notMembers termLike =
        Lens.foldMapOf foldElements (notMember termLike) normalizedAc

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
                Domain.wrapAc emptyNormalizedAc { opaque = [opaque1, opaque2] }
            }
        & mkBuiltin
        & makeSimplified
        & MultiAnd.singleton

    makeSimplifiedPredicate =
        OrCondition.fromPredicate
        . Predicate.markSimplifiedMaybeConditional Nothing

    makeSimplified = makeSimplifiedPredicate . makeCeilPredicate_

foldElements
    ::  AcWrapper collection
    =>  InternalVariable variable
    =>  Lens.Fold
            (NormalizedAc collection (TermLike Concrete) (TermLike variable))
            (Element collection (TermLike variable))
foldElements =
    Lens.folding $ \normalizedAc ->
        let
            concreteElements' =
                concreteElements normalizedAc
                & Map.toList
                & map Domain.wrapConcreteElement
            symbolicElements' = elementsWithVariables normalizedAc
        in
            concreteElements' <> symbolicElements'

fromElement
    :: AcWrapper normalized
    => InternalVariable variable
    => Element normalized (TermLike variable)
    -> NormalizedAc normalized (TermLike Concrete) (TermLike variable)
fromElement element
  | Just concreteKey <- Builtin.toKey symbolicKey
  = emptyNormalizedAc { concreteElements = Map.singleton concreteKey value }
  | otherwise
  = emptyNormalizedAc { elementsWithVariables = [element] }
  where
    (symbolicKey, value) = Domain.unwrapElement element
