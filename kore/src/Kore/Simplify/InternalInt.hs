{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Simplify.InternalInt (
    simplify,
) where

import Kore.Internal.InternalInt
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Prelude.Kore

simplify ::
    InternalInt ->
    OrPattern RewritingVariableName
simplify = OrPattern.fromPattern . pure . mkInternalInt
