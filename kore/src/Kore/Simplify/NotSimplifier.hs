{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
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

newtype NotSimplifier simplifier = NotSimplifier
    { runNotSimplifier ::
        SideCondition RewritingVariableName ->
        OrPattern RewritingVariableName ->
        simplifier (OrPattern RewritingVariableName)
    }
