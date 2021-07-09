{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.InternalList (
    simplify,
) where

import Data.Functor.Compose
import Kore.Internal.InternalList
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

simplify ::
    InternalList (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
simplify =
    traverse (Logic.scatter >>> Compose)
        >>> fmap mkInternalList
        >>> getCompose
        >>> fmap (Pattern.syncSort >>> fmap markSimplified)
        >>> MultiOr.observeAll
