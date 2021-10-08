{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Simplify.NotSimplifier (
    NotSimplifier (..),
) where

import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Syntax (
    Not,
    Sort,
 )

newtype NotSimplifier simplifier = NotSimplifier
    { runNotSimplifier ::
        SideCondition RewritingVariableName ->
        Not Sort (OrPattern RewritingVariableName) ->
        simplifier (OrPattern RewritingVariableName)
    }
