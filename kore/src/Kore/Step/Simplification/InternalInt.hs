{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.InternalInt (
    simplify,
) where

import Kore.Internal.InternalInt
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
    InternalInt ->
    OrPattern RewritingVariableName
simplify = OrPattern.fromPattern . pure . mkInternalInt
