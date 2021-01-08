{- |
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}

{-# LANGUAGE Strict #-}

module Kore.Step.Simplification.InternalSet
    ( simplify
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Data.Functor.Compose
import Data.Generics.Product

import qualified Kore.Builtin.AssociativeCommutative as Builtin
import Kore.Internal.InternalSet
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import qualified Logic


{-| Simplify an 'InternalMap' pattern.
-}
simplify
    :: InternalVariable variable
    => InternalSet (TermLike Concrete) (OrPattern variable)
    -> OrPattern variable
simplify =
    traverse (Logic.scatter >>> Compose)
    >>> fmap (normalizeInternalSet >>> markSimplified)
    >>> getCompose
    >>> fmap Pattern.syncSort
    >>> MultiOr.observeAll

normalizeInternalSet
    :: InternalVariable variable
    => InternalSet (TermLike Concrete) (TermLike variable)
    -> TermLike variable
normalizeInternalSet map' =
    case Lens.traverseOf (field @"builtinAcChild") Builtin.renormalize map' of
        Just normalizedSet ->
            -- If the InternalSet consists of a single compound, remove the
            -- wrapper around that term.
            getSingleOpaque normalizedSet
            -- Otherwise, inject the InternalSet into TermLike.
            & fromMaybe (mkInternalSet normalizedSet)
        _ -> mkBottom_
  where
    getSingleOpaque = asSingleOpaqueElem . getNormalizedAc
    getNormalizedAc = getNormalizedSet . builtinAcChild
