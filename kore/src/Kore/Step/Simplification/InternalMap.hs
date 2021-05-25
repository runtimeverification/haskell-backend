{- |
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
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
    Sort ->
    InternalMap Key (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
simplify sort =
    traverse (Logic.scatter >>> Compose)
        >>> fmap (normalizeInternalMap sort >>> markSimplified)
        >>> getCompose
        >>> fmap Pattern.syncSort
        >>> MultiOr.observeAll

normalizeInternalMap ::
    Sort ->
    InternalMap Key (TermLike RewritingVariableName) ->
    TermLike RewritingVariableName
normalizeInternalMap sort map' =
    case Lens.traverseOf (field @"builtinAcChild") Builtin.renormalize map' of
        Just normalizedMap ->
            -- If the InternalMap consists of a single compound, remove the
            -- wrapper around that term.
            getSingleOpaque normalizedMap
                -- Otherwise, inject the InternalMap into TermLike.
                & fromMaybe (mkInternalMap normalizedMap)
        _ -> mkBottom sort
  where
    getSingleOpaque = asSingleOpaqueElem . getNormalizedAc
    getNormalizedAc = getNormalizedMap . builtinAcChild
