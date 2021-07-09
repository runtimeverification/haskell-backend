{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.InternalBool (
    simplify,
) where

import Kore.Internal.InternalBool
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
    InternalBool ->
    OrPattern RewritingVariableName
simplify = OrPattern.fromPattern . pure . mkInternalBool
