{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Builtin.AssocComm.CeilSimplifier (
    newSetCeilSimplifier,
    newMapCeilSimplifier,
    generalizeMapElement,
) where

import Control.Error (
    MaybeT,
 )
import Control.Monad.Reader (
    MonadReader,
 )
import Data.Bifunctor qualified as Bifunctor
import Data.HashMap.Strict qualified as HashMap
import Data.HashSet qualified as HashSet
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
 )
import Kore.Attribute.Pattern.FreeVariables qualified as FreeVariables
import Kore.Internal.From (fromCeil_, fromEquals_, fromNot)
import Kore.Internal.InternalMap
import Kore.Internal.InternalSet
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.NormalForm (NormalForm)
import Kore.Internal.Predicate (
    Predicate,
    makeCeilPredicate,
    makeForallPredicate,
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.TermLike (
    Ceil (..),
    ElementVariable,
    InternalVariable,
    Key,
    TermLike,
    fromVariableName,
    generatedId,
    retractKey,
    termLikeSort,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.CeilSimplifier
import Kore.Simplify.Simplify (
    MonadSimplify,
 )
import Kore.Variables.Fresh (
    refreshElementVariable,
 )
import Prelude.Kore

type BuiltinAssocComm normalized variable =
    InternalAc Key normalized (TermLike variable)

type MkBuiltinAssocComm normalized variable =
    BuiltinAssocComm normalized variable -> TermLike variable

type MkNotMember normalized variable =
    Element normalized (TermLike variable) ->
    TermLike variable ->
    Predicate variable

newSetCeilSimplifier ::
    forall simplifier.
    MonadReader (SideCondition RewritingVariableName) simplifier =>
    MonadSimplify simplifier =>
    CeilSimplifier
        simplifier
        (BuiltinAssocComm NormalizedSet RewritingVariableName)
        NormalForm
newSetCeilSimplifier =
    CeilSimplifier $ \ceil@Ceil{ceilChild} -> do
        let mkInternalAc normalizedAc =
                ceilChild{builtinAcChild = wrapAc normalizedAc}
            mkNotMember element termLike =
                mkInternalAc (fromElement element){opaque = [termLike]}
                    & TermLike.mkInternalSet
                    & makeCeilPredicate
                    -- TODO (thomas.tuegel): Do not mark this simplified.
                    -- Marking here may prevent user-defined axioms from applying.
                    -- At present, we wouldn't apply such an axiom, anyway.
                    & Predicate.markSimplifiedMaybeConditional Nothing
        runCeilSimplifier
            ( newBuiltinAssocCommCeilSimplifier
                TermLike.mkInternalSet
                mkNotMember
            )
            ceil

-- {-# SPECIALIZE newSetCeilSimplifier ::
--     CeilSimplifier
--         Simplifier
--         (BuiltinAssocComm NormalizedSet RewritingVariableName)
--         NormalForm #-}

newMapCeilSimplifier ::
    forall simplifier.
    MonadReader (SideCondition RewritingVariableName) simplifier =>
    MonadSimplify simplifier =>
    CeilSimplifier
        simplifier
        (BuiltinAssocComm NormalizedMap RewritingVariableName)
        NormalForm
newMapCeilSimplifier =
    CeilSimplifier $ \ceil@Ceil{ceilChild} -> do
        let mkInternalAc normalizedAc =
                ceilChild{builtinAcChild = wrapAc normalizedAc}
            mkNotMember element termLike =
                mkInternalAc (fromElement element'){opaque = [termLike]}
                    & TermLike.mkInternalMap
                    & makeCeilPredicate
                    -- TODO (thomas.tuegel): Do not mark this simplified.
                    -- Marking here may prevent user-defined axioms from applying.
                    -- At present, we wouldn't apply such an axiom, anyway.
                    & Predicate.markSimplifiedMaybeConditional Nothing
                    & makeForallPredicate variable
              where
                (variable, element') =
                    generalizeMapElement
                        (TermLike.freeVariables termLike)
                        element
        runCeilSimplifier
            ( newBuiltinAssocCommCeilSimplifier
                TermLike.mkInternalMap
                mkNotMember
            )
            ceil

-- {-# SPECIALIZE newMapCeilSimplifier ::
--     CeilSimplifier
--         Simplifier
--         (BuiltinAssocComm NormalizedMap RewritingVariableName)
--         NormalForm #-}

{- | Generalize a 'MapElement' by replacing the 'MapValue' with a variable.

The variable is renamed if required to avoid the given 'FreeVariables' and any
variables in the key of the 'MapElement'. The variable is returned along with
the generalized 'MapElement'
-}
generalizeMapElement ::
    forall variable.
    InternalVariable variable =>
    FreeVariables variable ->
    MapElement (TermLike variable) ->
    (ElementVariable variable, MapElement (TermLike variable))
generalizeMapElement freeVariables' element =
    (variable, element')
  where
    (key, MapValue value) = unwrapElement element
    element' = wrapElement (key, MapValue $ TermLike.mkElemVar variable)
    avoiding =
        TermLike.freeVariables key <> freeVariables'
            & FreeVariables.toNames
    x =
        TermLike.mkElementVariable (generatedId "x") (termLikeSort value)
            & (fmap . fmap) (fromVariableName @variable)
    variable = refreshElementVariable avoiding x & fromMaybe x

newBuiltinAssocCommCeilSimplifier ::
    forall normalized simplifier.
    MonadReader (SideCondition RewritingVariableName) simplifier =>
    Ord (Element normalized (TermLike RewritingVariableName)) =>
    Ord (Value normalized (TermLike RewritingVariableName)) =>
    Hashable (Element normalized (TermLike RewritingVariableName)) =>
    Hashable (Value normalized (TermLike RewritingVariableName)) =>
    MonadSimplify simplifier =>
    Traversable (Value normalized) =>
    AcWrapper normalized =>
    MkBuiltinAssocComm normalized RewritingVariableName ->
    MkNotMember normalized RewritingVariableName ->
    CeilSimplifier
        simplifier
        (BuiltinAssocComm normalized RewritingVariableName)
        NormalForm
newBuiltinAssocCommCeilSimplifier mkBuiltin mkNotMember =
    CeilSimplifier $ \Ceil{ceilChild} -> do
        let internalAc@InternalAc{builtinAcChild} = ceilChild
            symbolicKeys = getSymbolicKeysOfAc builtinAcChild
            symbolicValues = getSymbolicValuesOfAc builtinAcChild
            concreteValues = getConcreteValuesOfAc builtinAcChild
            opaqueElements = opaque . unwrapAc $ builtinAcChild
            definedKeysAndOpaque =
                MultiAnd.make $ fromCeil_ <$> symbolicKeys <> opaqueElements
            definedValues =
                foldMap defineValue (symbolicValues <> concreteValues)
        definedSubCollections <-
            definePairWiseElements mkBuiltin mkNotMember internalAc
                . generatePairWiseElements
                $ builtinAcChild
        let conditions =
                definedKeysAndOpaque
                    <> definedValues
                    <> definedSubCollections
        return (MultiOr.singleton conditions)
  where
    defineValue ::
        Value normalized (TermLike RewritingVariableName) ->
        (MultiAnd (Predicate RewritingVariableName))
    defineValue = foldMap (MultiAnd.singleton . fromCeil_)

-- {-# SPECIALIZE newBuiltinAssocCommCeilSimplifier ::
--     forall normalized.
--     Ord (Element normalized (TermLike RewritingVariableName)) =>
--     Ord (Value normalized (TermLike RewritingVariableName)) =>
--     Hashable (Element normalized (TermLike RewritingVariableName)) =>
--     Hashable (Value normalized (TermLike RewritingVariableName)) =>
--     Traversable (Value normalized) =>
--     AcWrapper normalized =>
--     MkBuiltinAssocComm normalized RewritingVariableName ->
--     MkNotMember normalized RewritingVariableName ->
--     CeilSimplifier
--         Simplifier
--         (BuiltinAssocComm normalized RewritingVariableName)
--         (OrCondition RewritingVariableName) #-}

definePairWiseElements ::
    forall normalized simplifier.
    Ord (Element normalized (TermLike RewritingVariableName)) =>
    Hashable (Element normalized (TermLike RewritingVariableName)) =>
    MonadSimplify simplifier =>
    AcWrapper normalized =>
    MkBuiltinAssocComm normalized RewritingVariableName ->
    MkNotMember normalized RewritingVariableName ->
    InternalAc Key normalized (TermLike RewritingVariableName) ->
    PairWiseElements normalized Key (TermLike RewritingVariableName) ->
    MaybeT simplifier (MultiAnd (Predicate RewritingVariableName))
definePairWiseElements mkBuiltin mkNotMember internalAc pairWiseElements = do
    definedKeyPairs <-
        traverse
            distinctKey
            ( symbolicKeyPairs <> symbolicConcreteKeyPairs
                & HashSet.toList
            )
            & fmap MultiAnd.make
    let definedElementOpaquePairs =
            foldMap
                notMember
                (symbolicOpaquePairs <> concreteOpaquePairs')
        definedOpaquePairs =
            foldMap defineOpaquePair opaquePairs
    return . fold $
        [ definedKeyPairs
        , definedElementOpaquePairs
        , definedOpaquePairs
        ]
  where
    PairWiseElements
        { symbolicPairs
        , opaquePairs
        , symbolicConcretePairs
        , symbolicOpaquePairs
        , concreteOpaquePairs
        } = pairWiseElements
    symbolicKeyPairs =
        HashSet.map
            ( Bifunctor.bimap
                (fst . unwrapElement)
                (fst . unwrapElement)
                . acPairToPair
            )
            symbolicPairs
    symbolicConcreteKeyPairs =
        HashSet.map
            ( Bifunctor.bimap
                (fst . unwrapElement)
                (from @Key @(TermLike _) . fst)
            )
            symbolicConcretePairs
    concreteOpaquePairs' =
        HashSet.map
            ( Bifunctor.first
                wrapConcreteElement
            )
            concreteOpaquePairs

    distinctKey ::
        ( TermLike RewritingVariableName
        , TermLike RewritingVariableName
        ) ->
        MaybeT simplifier (Predicate RewritingVariableName)
    distinctKey (t1, t2) = do
        return (fromNot (fromEquals_ tMin tMax))
      where
        -- Stabilize the order of terms under Equals.
        (tMin, tMax) = minMax t1 t2

    notMember ::
        ( Element normalized (TermLike RewritingVariableName)
        , TermLike RewritingVariableName
        ) ->
        MultiAnd (Predicate RewritingVariableName)
    notMember (element, termLike) =
        mkNotMember element termLike
            & MultiAnd.singleton

    defineOpaquePair ::
        AcPair (TermLike RewritingVariableName) ->
        MultiAnd (Predicate RewritingVariableName)
    defineOpaquePair (AcPair opaque1 opaque2) =
        internalAc
            { builtinAcChild =
                wrapAc
                    emptyNormalizedAc{opaque = [opaque1, opaque2]}
            }
            & mkBuiltin
            & makeCeilPredicate
            -- TODO (thomas.tuegel): Do not mark this simplified.
            -- Marking here may prevent user-defined axioms from applying.
            -- At present, we wouldn't apply such an axiom, anyway.
            & Predicate.markSimplifiedMaybeConditional Nothing
            & MultiAnd.singleton

-- {-# SPECIALIZE definePairWiseElements ::
--     forall normalized.
--     Ord (Element normalized (TermLike RewritingVariableName)) =>
--     Hashable (Element normalized (TermLike RewritingVariableName)) =>
--     AcWrapper normalized =>
--     MkBuiltinAssocComm normalized RewritingVariableName ->
--     MkNotMember normalized RewritingVariableName ->
--     InternalAc Key normalized (TermLike RewritingVariableName) ->
--     PairWiseElements normalized Key (TermLike RewritingVariableName) ->
--     MaybeT Simplifier (MultiAnd (OrCondition RewritingVariableName)) #-}

fromElement ::
    AcWrapper normalized =>
    Element normalized (TermLike RewritingVariableName) ->
    NormalizedAc normalized Key (TermLike RewritingVariableName)
fromElement element
    | Just concreteKey <- retractKey symbolicKey =
        emptyNormalizedAc
            { concreteElements =
                HashMap.singleton concreteKey value
            }
    | otherwise =
        emptyNormalizedAc{elementsWithVariables = [element]}
  where
    (symbolicKey, value) = unwrapElement element
