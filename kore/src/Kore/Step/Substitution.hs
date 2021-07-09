{- |
Module      : Kore.Step.Substitution
Description : Tools for manipulating substitutions when doing Kore execution.
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Substitution (
    mergePredicatesAndSubstitutions,
    normalize,
) where

import Kore.Internal.Condition (
    Condition,
    Conditional (..),
 )
import qualified Kore.Internal.MultiOr as MultiOr
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.Substitution (
    Substitution,
 )
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Simplification.SubstitutionSimplifier (
    SubstitutionSimplifier (..),
 )
import qualified Kore.Step.Simplification.SubstitutionSimplifier as SubstitutionSimplifier
import Kore.TopBottom (
    TopBottom,
 )
import Logic
import Prelude.Kore

-- | Normalize the substitution and predicate of 'expanded'.
normalize ::
    forall term simplifier.
    Ord term =>
    TopBottom term =>
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Conditional RewritingVariableName term ->
    LogicT simplifier (Conditional RewritingVariableName term)
normalize sideCondition conditional@Conditional{substitution} = do
    results <- simplifySubstitution sideCondition substitution & lift
    scatter (MultiOr.map applyTermPredicate results)
  where
    applyTermPredicate =
        Pattern.andCondition conditional{substitution = mempty}
    SubstitutionSimplifier{simplifySubstitution} =
        SubstitutionSimplifier.substitutionSimplifier

{- |'mergePredicatesAndSubstitutions' merges a list of substitutions into
a single one, then merges the merge side condition and the given condition list
into a condition.

If it does not know how to merge the substitutions, it will transform them into
predicates and redo the merge.
-}
mergePredicatesAndSubstitutions ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    [Predicate RewritingVariableName] ->
    [Substitution RewritingVariableName] ->
    LogicT simplifier (Condition RewritingVariableName)
mergePredicatesAndSubstitutions topCondition predicates substitutions =
    simplifyCondition
        topCondition
        Conditional
            { term = ()
            , predicate = Predicate.makeMultipleAndPredicate predicates
            , substitution = fold substitutions
            }
