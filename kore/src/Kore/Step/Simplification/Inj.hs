{-# LANGUAGE Strict #-}

{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Step.Simplification.Inj (
    simplify,
) where

import Control.Lens as Lens
import Data.Generics.Product (
    field,
 )
import Kore.Internal.Condition as Condition
import Kore.Internal.MultiOr (
    MultiOr,
 )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Simplification.InjSimplifier (
    InjSimplifier (..),
 )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.TopBottom (
    TopBottom,
 )
import Prelude.Kore

-- |'simplify' simplifies an 'Inj' of 'OrPattern'.
simplify ::
    MonadSimplify simplifier =>
    Inj (OrPattern RewritingVariableName) ->
    simplifier (OrPattern RewritingVariableName)
simplify injOrPattern = do
    let composed = MultiOr.map liftConditional $ distributeOr injOrPattern
    InjSimplifier{evaluateInj} <- askInjSimplifier
    let evaluated = MultiOr.map (fmap evaluateInj) composed
    return evaluated

distributeOr ::
    Ord a =>
    TopBottom a =>
    Inj (MultiOr a) ->
    MultiOr (Inj a)
distributeOr inj@Inj{injChild} =
    MultiOr.map (flip (Lens.set (field @"injChild")) inj) injChild

liftConditional ::
    Inj (Conditional RewritingVariableName term) ->
    Conditional RewritingVariableName (Inj term)
liftConditional = sequenceA
