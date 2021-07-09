{- |
Copyright   : (c) Runtime Verification, 2020
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
import qualified Control.Monad.Reader as Reader
import qualified Data.Bifunctor as Bifunctor
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
 )
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Internal.InternalMap
import Kore.Internal.InternalSet
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.OrCondition (
    OrCondition,
 )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.Predicate (
    Predicate,
    makeCeilPredicate,
    makeForallPredicate,
 )
import qualified Kore.Internal.Predicate as Predicate
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
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Step.Simplification.AndPredicates as And
import Kore.Step.Simplification.CeilSimplifier
import qualified Kore.Step.Simplification.Equals as Equals
import qualified Kore.Step.Simplification.Not as Not
import Kore.Step.Simplification.Simplify (
    MonadSimplify,
    makeEvaluateTermCeil,
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
        (OrCondition RewritingVariableName)
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

newMapCeilSimplifier ::
    forall simplifier.
    MonadReader (SideCondition RewritingVariableName) simplifier =>
    MonadSimplify simplifier =>
    CeilSimplifier
        simplifier
        (BuiltinAssocComm NormalizedMap RewritingVariableName)
        (OrCondition RewritingVariableName)
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
        (OrCondition RewritingVariableName)
newBuiltinAssocCommCeilSimplifier mkBuiltin mkNotMember =
    CeilSimplifier $ \Ceil{ceilChild} -> do
        let internalAc@InternalAc{builtinAcChild} = ceilChild
        sideCondition <- Reader.ask
        let symbolicKeys = getSymbolicKeysOfAc builtinAcChild
            symbolicValues = getSymbolicValuesOfAc builtinAcChild
            concreteValues = getConcreteValuesOfAc builtinAcChild
            opaqueElements = opaque . unwrapAc $ builtinAcChild
        definedKeysAndOpaque <-
            traverse
                (makeEvaluateTermCeil sideCondition)
                (symbolicKeys <> opaqueElements)
                & fmap MultiAnd.make
        definedValues <-
            traverse
                (defineValue sideCondition)
                (symbolicValues <> concreteValues)
                & fmap mconcat
        definedSubCollections <-
            definePairWiseElements mkBuiltin mkNotMember internalAc
                . generatePairWiseElements
                $ builtinAcChild
        let conditions =
                definedKeysAndOpaque
                    <> definedValues
                    <> definedSubCollections
        And.simplifyEvaluatedMultiPredicate sideCondition conditions
  where
    defineValue ::
        SideCondition RewritingVariableName ->
        Value normalized (TermLike RewritingVariableName) ->
        MaybeT
            simplifier
            (MultiAnd (OrCondition RewritingVariableName))
    defineValue sideCondition = foldlM worker mempty
      where
        worker multiAnd termLike = do
            evaluated <- makeEvaluateTermCeil sideCondition termLike
            return (multiAnd <> MultiAnd.singleton evaluated)

definePairWiseElements ::
    forall normalized simplifier.
    Ord (Element normalized (TermLike RewritingVariableName)) =>
    Hashable (Element normalized (TermLike RewritingVariableName)) =>
    MonadSimplify simplifier =>
    MonadReader (SideCondition RewritingVariableName) simplifier =>
    AcWrapper normalized =>
    MkBuiltinAssocComm normalized RewritingVariableName ->
    MkNotMember normalized RewritingVariableName ->
    InternalAc Key normalized (TermLike RewritingVariableName) ->
    PairWiseElements normalized Key (TermLike RewritingVariableName) ->
    MaybeT simplifier (MultiAnd (OrCondition RewritingVariableName))
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
        MaybeT simplifier (OrCondition RewritingVariableName)
    distinctKey (t1, t2) = do
        sideCondition <- Reader.ask
        Equals.makeEvaluateTermsToPredicate tMin tMax sideCondition
            >>= Not.simplifyEvaluatedPredicate
      where
        -- Stabilize the order of terms under Equals.
        (tMin, tMax) = minMax t1 t2

    notMember ::
        ( Element normalized (TermLike RewritingVariableName)
        , TermLike RewritingVariableName
        ) ->
        MultiAnd (OrCondition RewritingVariableName)
    notMember (element, termLike) =
        mkNotMember element termLike
            & OrCondition.fromPredicate
            & MultiAnd.singleton

    defineOpaquePair ::
        AcPair (TermLike RewritingVariableName) ->
        MultiAnd (OrCondition RewritingVariableName)
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
            & OrCondition.fromPredicate
            & MultiAnd.singleton

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
