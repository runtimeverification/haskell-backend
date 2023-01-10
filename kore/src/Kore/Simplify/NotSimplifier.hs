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

{- | We use this class to break a module import loop. Its sole instance
 is in "Kore.Simplify.Not":

 @
 instance simplifier ~ 'Kore.Simplify.Simplify.Simplifier' => NotSimplifier simplifier where
   notSimplifier = "Kore.Simplify.Not".'Kore.Simplify.Not.simplify'
 @
-}
class NotSimplifier simplifier | -> simplifier where
    notSimplifier ::
        SideCondition RewritingVariableName ->
        Not Sort (OrPattern RewritingVariableName) ->
        simplifier (OrPattern RewritingVariableName)
