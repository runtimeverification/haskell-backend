{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}
module Kore.Step.Simplification.InternalMap
    ( simplify
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Data.Functor.Compose
import Data.Generics.Product

import qualified Kore.Builtin.AssociativeCommutative as Builtin
import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.Conditional
    ( Conditional
    )
import Kore.Internal.InternalMap
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
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
    => InternalMap (TermLike Concrete) (OrPattern variable)
    -> OrPattern variable
simplify internalMap =
    MultiOr.observeAll $ do
        child <- simplifyInternalMap normalizeInternalMap internalMap
        return (markSimplified <$> child)

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
    mkBuiltinMap map'
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
    getNormalizedAc = getNormalizedMap . Domain.builtinAcChild
