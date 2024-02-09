{- |
Module      : Kore.Rewrite.Substitution
Description : Tools for manipulating substitutions when doing Kore execution.
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Rewrite.Substitution (
    mergePredicatesAndSubstitutions,
    normalize,
) where

import Kore.Internal.Condition (
    Condition,
    Conditional (..),
 )
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (
    Predicate,
 )
import Kore.Internal.Predicate qualified as Predicate
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.Substitution (
    Substitution,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify as Simplifier
import Kore.Simplify.SubstitutionSimplifier (
    SubstitutionSimplifier (..),
 )
import Kore.Simplify.SubstitutionSimplifier qualified as SubstitutionSimplifier
import Kore.TopBottom (
    TopBottom,
 )
import Logic
import Prelude.Kore

-- | Normalize the substitution and predicate of 'expanded'.
normalize ::
    forall term.
    Ord term =>
    TopBottom term =>
    SideCondition RewritingVariableName ->
    Conditional RewritingVariableName term ->
    LogicT Simplifier (Conditional RewritingVariableName term)
normalize sideCondition conditional@Conditional{substitution} = do
    results <- simplifySubstitution sideCondition substitution & lift
    scatter (MultiOr.map applyTermPredicate results)
    where
        applyTermPredicate =
            Pattern.andCondition conditional{substitution = mempty}
        SubstitutionSimplifier{simplifySubstitution} =
            SubstitutionSimplifier.substitutionSimplifier

{- | 'mergePredicatesAndSubstitutions' merges a list of substitutions into
a single one, then merges the merge side condition and the given condition list
into a condition.

If it does not know how to merge the substitutions, it will transform them into
predicates and redo the merge.
-}
mergePredicatesAndSubstitutions ::
    SideCondition RewritingVariableName ->
    [Predicate RewritingVariableName] ->
    [Substitution RewritingVariableName] ->
    LogicT Simplifier (Condition RewritingVariableName)
mergePredicatesAndSubstitutions topCondition predicates substitutions =
    simplifyCondition
        topCondition
        Conditional
            { term = ()
            , predicate = Predicate.makeMultipleAndPredicate predicates
            , substitution = fold substitutions
            }
