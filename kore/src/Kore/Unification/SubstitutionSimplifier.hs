{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Unification.SubstitutionSimplifier (
    substitutionSimplifier,
    unificationMakeAnd,

    -- * Re-exports
    module Kore.Simplify.SubstitutionSimplifier,
) where

import Control.Error (
    MaybeT,
    maybeT,
 )
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.OrCondition qualified as OrCondition
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Conditional qualified as Conditional
import Kore.Internal.Predicate (
    Predicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.Substitution (
    Normalization,
    Substitution,
 )
import Kore.Internal.TermLike (
    TermLike,
 )
import Kore.Log.DebugSubstitutionSimplifier (
    debugSubstitutionSimplifierResult,
    whileDebugSubstitutionSimplifier,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.NotSimplifier
import Kore.Unification.Procedure (unificationProcedure)
import Kore.Unification.NewUnifier (NewUnifier)
import Kore.Simplify.Simplify qualified as Simplifier
import Kore.Simplify.SubstitutionSimplifier (
    MakeAnd (..),
    SubstitutionSimplifier (..),
    deduplicateSubstitution,
    simplifySubstitutionWorker,
 )
import Kore.TopBottom qualified as TopBottom
import Kore.Unification.Unify
import Logic qualified
import Prelude.Kore


-- TODO: refactor, now that we've removed the dependency on the
-- not simplifier
{- | A 'SubstitutionSimplifier' to use during unification.

If multiple assignments to a single variable cannot be unified, this simplifier
uses 'Unifier.throwUnificationError'.
-}
substitutionSimplifier :: SubstitutionSimplifier NewUnifier
substitutionSimplifier =
    SubstitutionSimplifier wrapper
  where
    wrapper ::
        SideCondition RewritingVariableName ->
        Substitution RewritingVariableName ->
        NewUnifier (OrCondition RewritingVariableName)
    wrapper sideCondition substitution =
        whileDebugSubstitutionSimplifier $ do
            (predicate, result) <-
                worker substitution
                    & maybeT empty return
            let condition = Condition.fromNormalizationSimplified result
            let condition' = Condition.fromPredicate predicate <> condition
                conditions = OrCondition.fromCondition condition'
            TopBottom.guardAgainstBottom conditions
            debugSubstitutionSimplifierResult
            return conditions
      where
        worker ::
            Substitution RewritingVariableName ->
            MaybeT
                NewUnifier
                ( Predicate RewritingVariableName
                , Normalization RewritingVariableName
                )
        worker =
            simplifySubstitutionWorker
                sideCondition
                unificationMakeAnd

unificationMakeAnd :: MakeAnd NewUnifier
unificationMakeAnd =
    MakeAnd{makeAnd}
  where
    makeAnd ::
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        SideCondition RewritingVariableName ->
        NewUnifier (Pattern RewritingVariableName)
    makeAnd termLike1 termLike2 sideCondition = do
        unified <- unificationProcedure sideCondition termLike1 termLike2
        Simplifier.simplifyCondition
            sideCondition
            -- Since this is \\and unification, we default to returning the first term
            (Conditional.withCondition termLike1 unified)
            & Logic.lowerLogicT
