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
import Kore.Internal.InternalMap
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import qualified Logic

{-| 'simplify' simplifies a 'DomainValue' pattern, which means returning
an or containing a term made of that value.
-}
simplify
    :: InternalVariable variable
    => InternalMap (TermLike Concrete) (OrPattern variable)
    -> OrPattern variable
simplify =
    traverse (Logic.scatter >>> Compose)
    >>> fmap (normalizeInternalMap >>> normalizedMapResultToTerm)
    >>> getCompose
    >>> fmap (Pattern.syncSort >>> fmap markSimplified)
    >>> MultiOr.observeAll

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
            (asSingleOpaqueElem . getNormalizedAc) normalizedMap
            & maybe (NormalizedMapResult normalizedMap) SingleOpaqueElemResult
        _ -> BottomResult
  where
    getNormalizedAc = getNormalizedMap . builtinAcChild
