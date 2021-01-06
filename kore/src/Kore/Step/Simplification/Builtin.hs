{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}
module Kore.Step.Simplification.Builtin
    ( simplify
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Data.Functor.Compose
import Data.Generics.Product

import qualified Kore.Builtin.AssociativeCommutative as Builtin
import Kore.Domain.Builtin
    ( InternalMap
    , InternalSet
    )
import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.Conditional
    ( Conditional
    )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Predicate
    ( makeFalsePredicate_
    )
import Kore.Internal.TermLike
import Logic
    ( Logic
    )
import qualified Logic

{-| 'simplify' simplifies a 'DomainValue' pattern, which means returning
an or containing a term made of that value.
-}
simplify
    :: InternalVariable variable
    => Builtin (OrPattern variable)
    -> OrPattern variable
simplify builtin =
    MultiOr.observeAll $ do
        child <- simplifyBuiltin builtin
        return (markSimplified <$> child)

simplifyBuiltin
    :: InternalVariable variable
    => Builtin (OrPattern variable)
    -> Logic (Conditional variable (TermLike variable))
simplifyBuiltin =
    \case
        Domain.BuiltinMap map' ->
            simplifyInternalMap normalizeInternalMap map'
        Domain.BuiltinSet set' ->
            fmap mkBuiltin <$> simplifyInternalSet set'

simplifyInternal
    :: (InternalVariable variable, Traversable t)
    => (t (TermLike variable) -> Maybe (t (TermLike variable)))
    -> t (OrPattern variable)
    -> Logic (Conditional variable (t (TermLike variable)))
simplifyInternal normalizer tOrPattern = do
    conditional <- sequenceA <$> traverse Logic.scatter tOrPattern
    let bottom = conditional `Conditional.andPredicate` makeFalsePredicate_
        normalized = fromMaybe bottom $ traverse normalizer conditional
    return normalized

simplifyInternalMap
    :: InternalVariable variable
    => ( InternalMap (TermLike Concrete) (TermLike variable)
        -> NormalizedMapResult variable
       )
    -> InternalMap (TermLike Concrete) (OrPattern variable)
    -> Logic (Conditional variable (TermLike variable))
simplifyInternalMap normalizer tOrPattern = do
    conditional <- getCompose $ traverse (Compose . Logic.scatter) tOrPattern
    let normalized = normalizedMapResultToTerm . normalizer <$> conditional
    return normalized

data NormalizedMapResult variable =
    NormalizedMapResult (InternalMap (TermLike Concrete) (TermLike variable))
    | SingleOpaqueElemResult (TermLike variable)
    | BottomResult

normalizedMapResultToTerm
    :: InternalVariable variable
    => NormalizedMapResult variable
    -> TermLike variable
normalizedMapResultToTerm (NormalizedMapResult map') =
    mkBuiltin . Domain.BuiltinMap $ map'
normalizedMapResultToTerm (SingleOpaqueElemResult opaqueElem) =
    opaqueElem
normalizedMapResultToTerm BottomResult =
    mkBottom_

normalizeInternalMap
    :: Ord variable
    => InternalMap (TermLike Concrete) (TermLike variable)
    -> NormalizedMapResult variable
normalizeInternalMap map' =
    case Lens.traverseOf (field @"builtinAcChild") Builtin.renormalize map' of
        Just normalizedMap ->
            maybe
                (NormalizedMapResult normalizedMap)
                SingleOpaqueElemResult
                $ Domain.asSingleOpaqueElem
                    . getNormalizedAc
                    $ normalizedMap
        _ -> BottomResult
  where
    getNormalizedAc = Domain.getNormalizedMap . Domain.builtinAcChild

simplifyInternalSet
    :: InternalVariable variable
    => Domain.InternalSet (TermLike Concrete) (OrPattern variable)
    -> Logic (Conditional variable (Builtin (TermLike variable)))
simplifyInternalSet =
    (fmap . fmap) Domain.BuiltinSet
    . simplifyInternal normalizeInternalSet

normalizeInternalSet
    :: Ord variable
    => InternalSet (TermLike Concrete) (TermLike variable)
    -> Maybe (InternalSet (TermLike Concrete) (TermLike variable))
normalizeInternalSet =
    Lens.traverseOf (field @"builtinAcChild") Builtin.renormalize
