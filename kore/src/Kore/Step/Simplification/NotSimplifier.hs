{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Step.Simplification.NotSimplifier (
    NotSimplifier (..),
) where

import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )

newtype NotSimplifier simplifier = NotSimplifier
    { runNotSimplifier ::
        SideCondition RewritingVariableName ->
        OrPattern RewritingVariableName ->
        simplifier (OrPattern RewritingVariableName)
    }
