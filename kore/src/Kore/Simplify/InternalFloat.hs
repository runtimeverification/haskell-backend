{- |
Copyright   : (c) Runtime Verification, 2026
License     : BSD-3-Clause
-}
module Kore.Simplify.InternalFloat (
    simplify,
) where

import Kore.Internal.InternalFloat
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Prelude.Kore

simplify ::
    InternalFloat ->
    OrPattern RewritingVariableName
simplify = OrPattern.fromPattern . pure . mkInternalFloat
