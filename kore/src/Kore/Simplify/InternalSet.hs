{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Simplify.InternalSet (
    simplify,
) where

import qualified Control.Lens as Lens
import Data.Functor.Compose
import Data.Generics.Product
import qualified Kore.Builtin.AssociativeCommutative as Builtin
import Kore.Internal.InternalSet
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Logic
import Prelude.Kore

-- | Simplify an 'InternalMap' pattern.
simplify ::
    Sort ->
    InternalSet Key (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
simplify sort =
    traverse (Logic.scatter >>> Compose)
        >>> fmap (normalizeInternalSet sort >>> markSimplified)
        >>> getCompose
        >>> fmap Pattern.syncSort
        >>> MultiOr.observeAll

normalizeInternalSet ::
    Sort ->
    InternalSet Key (TermLike RewritingVariableName) ->
    TermLike RewritingVariableName
normalizeInternalSet returnSort map' =
    case Lens.traverseOf (field @"builtinAcChild") Builtin.renormalize map' of
        Just normalizedSet ->
            -- If the InternalSet consists of a single compound, remove the
            -- wrapper around that term.
            getSingleOpaque normalizedSet
                -- Otherwise, inject the InternalSet into TermLike.
                & fromMaybe (mkInternalSet normalizedSet)
        _ -> mkBottom returnSort
  where
    getSingleOpaque = retractSingleOpaqueElem . getNormalizedAc
    getNormalizedAc = getNormalizedSet . builtinAcChild
