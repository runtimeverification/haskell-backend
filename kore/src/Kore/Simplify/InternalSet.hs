{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Simplify.InternalSet (
    simplify,
) where

import Control.Lens qualified as Lens
import Data.Functor.Compose
import Data.Generics.Product
import Kore.Builtin.AssociativeCommutative qualified as Builtin
import Kore.Internal.InternalSet
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Logic qualified
import Prelude.Kore

-- | Simplify an 'InternalMap' pattern.
simplify ::
    InternalSet Key (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
simplify internalSet =
    traverse (Logic.scatter >>> Compose) internalSet
        & fmap (normalizeInternalSet (builtinAcSort internalSet) >>> markSimplified)
        & getCompose
        & fmap Pattern.syncSort
        & MultiOr.observeAll

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
