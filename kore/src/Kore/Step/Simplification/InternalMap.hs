{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.InternalMap (
    simplify,
) where

import qualified Control.Lens as Lens
import Data.Functor.Compose
import Data.Generics.Product
import qualified Kore.Builtin.AssociativeCommutative as Builtin
import Kore.Internal.InternalMap
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import qualified Logic
import Prelude.Kore

-- | Simplify an 'InternalMap' pattern.
simplify ::
    InternalMap Key (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
simplify =
    traverse (Logic.scatter >>> Compose)
        >>> fmap (normalizeInternalMap >>> markSimplified)
        >>> getCompose
        >>> fmap Pattern.syncSort
        >>> MultiOr.observeAll

normalizeInternalMap ::
    InternalMap Key (TermLike RewritingVariableName) ->
    TermLike RewritingVariableName
normalizeInternalMap map' =
    case Lens.traverseOf (field @"builtinAcChild") Builtin.renormalize map' of
        Just normalizedMap ->
            -- If the InternalMap consists of a single compound, remove the
            -- wrapper around that term.
            getSingleOpaque normalizedMap
                -- Otherwise, inject the InternalMap into TermLike.
                & fromMaybe (mkInternalMap normalizedMap)
        _ -> mkBottom_
  where
    getSingleOpaque = asSingleOpaqueElem . getNormalizedAc
    getNormalizedAc = getNormalizedMap . builtinAcChild
