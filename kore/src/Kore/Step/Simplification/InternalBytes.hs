{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.InternalBytes (
    simplify,
) where

import Kore.Internal.InternalBytes
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
    InternalBytes ->
    OrPattern RewritingVariableName
simplify = OrPattern.fromPattern . pure . mkInternalBytes'
