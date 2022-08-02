{- |
Copyright   : (c) Runtime Verification, 2020-2021
License     : BSD-3-Clause
-}
module Kore.Simplify.NotSimplifier (
    NotSimplifier (..),
    mapNotSimplifier,
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

mapNotSimplifier ::
    (forall a. simplifier a -> simplifier' a) ->
    NotSimplifier simplifier -> NotSimplifier simplifier'
mapNotSimplifier f NotSimplifier{runNotSimplifier} =
    NotSimplifier {runNotSimplifier = \sd n -> f (runNotSimplifier sd n)}
