{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Simplify.InternalList (
    simplify,
) where

import Data.Functor.Compose
import Kore.Internal.InternalList
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

simplify ::
    InternalList (OrPattern RewritingVariableName) ->
    OrPattern RewritingVariableName
simplify =
    traverse (Logic.scatter >>> Compose)
        >>> fmap mkInternalList
        >>> getCompose
        >>> fmap (Pattern.syncSort >>> fmap markSimplified)
        >>> MultiOr.observeAll
