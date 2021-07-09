{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.InternalString (
    simplify,
) where

import Kore.Internal.InternalString
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Prelude.Kore

simplify ::
    InternalString ->
    OrPattern RewritingVariableName
simplify = OrPattern.fromPattern . pure . mkInternalString
