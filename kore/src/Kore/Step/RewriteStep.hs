{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause

Direct interface to rule application (step-wise execution).
See "Kore.Step" for the high-level strategy-based interface.
-}
module Kore.Step.RewriteStep (
    applyRewriteRulesParallel,
    withoutUnification,
    applyRewriteRulesSequence,
    applyClaimsSequence,
) where

import qualified Control.Monad.State.Strict as State
import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Sequence as Seq
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
 )
import Kore.Attribute.SourceLocation (
    SourceLocation,
 )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition (SideCondition)
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Log.DebugAppliedRewriteRules (
    debugAppliedRewriteRules,
 )
import Kore.Log.ErrorRewritesInstantiation (
    checkSubstitutionCoverage,
 )
import Kore.Rewriting.RewritingVariable
import Kore.Step.AxiomPattern (
    AxiomPattern,
 )
import Kore.Step.ClaimPattern (
    ClaimPattern (..),
 )
import qualified Kore.Step.ClaimPattern as Claim
import qualified Kore.Step.Remainder as Remainder
import qualified Kore.Step.Result as Result
import qualified Kore.Step.Result as Step
import Kore.Step.RulePattern (
    RewriteRule (..),
    RulePattern,
 )
import qualified Kore.Step.RulePattern as Rule
import Kore.Step.Simplification.Simplify (
    MonadSimplify,
    simplifyCondition,
 )
import Kore.Step.Step (
    Result,
    Results,
    UnifiedRule,
    applyInitialConditions,
    applyRemainder,
    assertFunctionLikeResults,
    unifyRules,
 )
import Kore.Substitute
import Logic (
    LogicT,
 )
import qualified Logic
import Prelude.Kore

withoutUnification :: UnifiedRule rule -> rule
withoutUnification = Conditional.term

{- | Produce the final configurations of an applied rule.

The rule's 'ensures' clause is applied to the conditions and normalized. The
substitution is applied to the right-hand side of the rule to produce the final
configurations.

Because the rule is known to apply, @finalizeAppliedRule@ always returns exactly
one branch.

See also: 'applyInitialConditions'
-}
finalizeAppliedRule ::
    forall simplifier.
    MonadSimplify simplifier =>
    -- | SideCondition containing metadata
    SideCondition RewritingVariableName ->
    -- | Applied rule
    RulePattern RewritingVariableName ->
    -- | Conditions of applied rule
    OrCondition RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
finalizeAppliedRule
    sideCondition
    renamedRule
    appliedConditions =
        MultiOr.observeAllT $
            finalizeAppliedRuleWorker =<< Logic.scatter appliedConditions
      where
        ruleRHS = Rule.rhs renamedRule
        finalizeAppliedRuleWorker appliedCondition = do
            -- Combine the initial conditions, the unification conditions, and the
            -- axiom ensures clause. The axiom requires clause is included by
            -- unifyRule.
            let avoidVars = freeVariables appliedCondition <> freeVariables ruleRHS
                finalPattern =
                    Rule.topExistsToImplicitForall avoidVars ruleRHS
            constructConfiguration
                sideCondition
                appliedCondition
                finalPattern

{- | Combine all the conditions to apply rule and construct the result.

@constructConfiguration@ combines:

* the applied condition (the initial condition, unification condition, and the
  rule's @requires@ clause), and
* the rule's @ensures@ clause

The parts of the applied condition were already combined by 'unifyRule'. First, the @ensures@ clause is simplified under the applied condition. Then, the conditions are conjoined and simplified again.
-}
constructConfiguration ::
    MonadSimplify simplifier =>
    -- | SideCondition containing metadata
    SideCondition RewritingVariableName ->
    -- | Applied condition
    Condition RewritingVariableName ->
    -- | Final configuration
    Pattern RewritingVariableName ->
    LogicT simplifier (Pattern RewritingVariableName)
constructConfiguration
    sideCondition
    appliedCondition
    finalPattern = do
        let ensuresCondition = Pattern.withoutTerm finalPattern
        finalCondition <-
            do
                partial <-
                    simplifyCondition
                        ( sideCondition
                            & SideCondition.addConditionWithReplacements
                                appliedCondition
                        )
                        ensuresCondition
                -- TODO (thomas.tuegel): It should not be necessary to simplify
                -- after conjoining the conditions.
                simplifyCondition sideCondition (appliedCondition <> partial)
                & Logic.lowerLogicT
        -- Apply the normalized substitution to the right-hand side of the
        -- axiom.
        let Conditional{substitution} = finalCondition
            substitution' = Substitution.toMap substitution
            Conditional{term = finalTerm} = finalPattern
            finalTerm' = substitute substitution' finalTerm
        -- TODO (thomas.tuegel): Should the final term be simplified after
        -- substitution?
        return (finalTerm' `Pattern.withCondition` finalCondition)

finalizeAppliedClaim ::
    forall simplifier.
    MonadSimplify simplifier =>
    -- | SideCondition containing metadata
    SideCondition RewritingVariableName ->
    -- | Applied rule
    ClaimPattern ->
    -- | Conditions of applied rule
    OrCondition RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
finalizeAppliedClaim sideCondition renamedRule appliedConditions =
    MultiOr.observeAllT $
        finalizeAppliedRuleWorker =<< Logic.scatter appliedConditions
  where
    ClaimPattern{right} = renamedRule
    finalizeAppliedRuleWorker appliedCondition =
        Claim.assertRefreshed renamedRule $ do
            finalPattern <- Logic.scatter right
            -- Combine the initial conditions, the unification conditions, and
            -- the axiom ensures clause. The axiom requires clause is included
            -- by unifyRule.
            constructConfiguration
                sideCondition
                appliedCondition
                finalPattern

type UnifyingRuleWithRepresentation representation rule =
    ( Rule.UnifyingRule representation
    , Rule.UnifyingRuleVariable representation ~ RewritingVariableName
    , Rule.UnifyingRule rule
    , Rule.UnifyingRuleVariable rule ~ RewritingVariableName
    , From rule (AxiomPattern RewritingVariableName)
    , From rule SourceLocation
    )

type FinalizeApplied rule simplifier =
    rule ->
    OrCondition RewritingVariableName ->
    LogicT simplifier (OrPattern RewritingVariableName)

finalizeRule ::
    UnifyingRuleWithRepresentation representation rule =>
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    (representation -> rule) ->
    FinalizeApplied representation simplifier ->
    FreeVariables RewritingVariableName ->
    -- | Initial conditions
    Pattern RewritingVariableName ->
    -- | Rewriting axiom
    UnifiedRule representation ->
    simplifier [Result representation]
finalizeRule
    sideCondition
    toRule
    finalizeApplied
    initialVariables
    initial
    unifiedRule =
        Logic.observeAllT $ do
            let initialCondition = Conditional.withoutTerm initial
            let unificationCondition = Conditional.withoutTerm unifiedRule
            applied <-
                applyInitialConditions
                    sideCondition
                    initialCondition
                    unificationCondition
            checkSubstitutionCoverage initial (toRule <$> unifiedRule)
            let renamedRule = Conditional.term unifiedRule
            final <- finalizeApplied renamedRule applied
            let result =
                    OrPattern.map (resetResultPattern initialVariables) final
            return Step.Result{appliedRule = unifiedRule, result}

-- | Finalizes a list of applied rules into 'Results'.
type Finalizer rule simplifier =
    MonadSimplify simplifier =>
    FreeVariables RewritingVariableName ->
    Pattern RewritingVariableName ->
    [UnifiedRule rule] ->
    simplifier (Results rule)

finalizeRulesParallel ::
    forall representation rule simplifier.
    UnifyingRuleWithRepresentation representation rule =>
    SideCondition RewritingVariableName ->
    (representation -> rule) ->
    FinalizeApplied representation simplifier ->
    Finalizer representation simplifier
finalizeRulesParallel
    sideCondition
    toRule
    finalizeApplied
    initialVariables
    initial
    unifiedRules =
        do
            results <-
                traverse
                    ( finalizeRule
                        sideCondition
                        toRule
                        finalizeApplied
                        initialVariables
                        initial
                    )
                    unifiedRules
                    & fmap fold
            let unifications = MultiOr.make (Conditional.withoutTerm <$> unifiedRules)
                remainder = Condition.fromPredicate (Remainder.remainder' unifications)
            remainders <-
                applyRemainder sideCondition initial remainder
                    & Logic.observeAllT
                    & fmap (fmap assertRemainderPattern >>> OrPattern.fromPatterns)
            return
                Step.Results
                    { results = Seq.fromList results
                    , remainders
                    }

finalizeSequence ::
    forall representation rule simplifier.
    UnifyingRuleWithRepresentation representation rule =>
    SideCondition RewritingVariableName ->
    (representation -> rule) ->
    FinalizeApplied representation simplifier ->
    Finalizer representation simplifier
finalizeSequence
    sideCondition
    toRule
    finalizeApplied
    initialVariables
    initial
    unifiedRules =
        do
            (results, remainder) <-
                State.runStateT
                    (traverse finalizeRuleSequence' unifiedRules)
                    (Conditional.withoutTerm initial)
            remainders <-
                applyRemainder sideCondition initial remainder
                    & Logic.observeAllT
                    & fmap (fmap assertRemainderPattern >>> OrPattern.fromPatterns)
            return
                Step.Results
                    { results = Seq.fromList $ fold results
                    , remainders
                    }
      where
        initialTerm = Conditional.term initial
        finalizeRuleSequence' unifiedRule = do
            remainder <- State.get
            let remainderPattern = Conditional.withCondition initialTerm remainder
            results <-
                finalizeRule
                    sideCondition
                    toRule
                    finalizeApplied
                    initialVariables
                    remainderPattern
                    unifiedRule
                    & Monad.Trans.lift
            let unification = Conditional.withoutTerm unifiedRule
                remainder' =
                    Condition.fromPredicate $
                        Remainder.remainder' $
                            MultiOr.singleton unification
            State.put (remainder `Conditional.andCondition` remainder')
            return results

applyWithFinalizer ::
    forall rule simplifier.
    MonadSimplify simplifier =>
    Rule.UnifyingRule rule =>
    Rule.UnifyingRuleVariable rule ~ RewritingVariableName =>
    From rule SourceLocation =>
    -- | SideCondition containing metadata
    SideCondition RewritingVariableName ->
    -- | Finalizing function
    Finalizer rule simplifier ->
    -- | Rewrite rules
    [rule] ->
    -- | Configuration being rewritten
    Pattern RewritingVariableName ->
    simplifier (Results rule)
applyWithFinalizer sideCondition finalize rules initial = do
    results <- unifyRules sideCondition initial rules
    debugAppliedRewriteRules initial (locations <$> results)
    let initialVariables = freeVariables initial
    finalize initialVariables initial results
  where
    locations = from @_ @SourceLocation . extract
{-# INLINE applyWithFinalizer #-}

{- | Apply the given rules to the initial configuration in parallel.

See also: 'applyRewriteRule'
-}
applyRulesParallel ::
    forall simplifier.
    MonadSimplify simplifier =>
    -- | SideCondition containing metadata
    SideCondition RewritingVariableName ->
    -- | Rewrite rules
    [RulePattern RewritingVariableName] ->
    -- | Configuration being rewritten
    Pattern RewritingVariableName ->
    simplifier (Results (RulePattern RewritingVariableName))
applyRulesParallel sideCondition rules initial =
    applyWithFinalizer
        sideCondition
        ( finalizeRulesParallel
            sideCondition
            RewriteRule
            (finalizeAppliedRule sideCondition)
        )
        rules
        initial

{- | Apply the given rewrite rules to the initial configuration in parallel.

See also: 'applyRewriteRule'
-}
applyRewriteRulesParallel ::
    forall simplifier.
    MonadSimplify simplifier =>
    -- | Rewrite rules
    [RewriteRule RewritingVariableName] ->
    -- | Configuration being rewritten
    Pattern RewritingVariableName ->
    simplifier (Results (RulePattern RewritingVariableName))
applyRewriteRulesParallel
    (map getRewriteRule -> rules)
    initial =
        do
            let sideCondition =
                    SideCondition.cacheSimplifiedFunctions
                        (Pattern.toTermLike initial)
            results <- applyRulesParallel sideCondition rules initial
            assertFunctionLikeResults (term initial) results
            return results

{- | Apply the given rewrite rules to the initial configuration in sequence.

See also: 'applyRewriteRule'
-}
applyRulesSequence ::
    forall simplifier.
    MonadSimplify simplifier =>
    -- | SideCondition containing metadata
    SideCondition RewritingVariableName ->
    -- | Rewrite rules
    [RulePattern RewritingVariableName] ->
    -- | Configuration being rewritten
    Pattern RewritingVariableName ->
    simplifier (Results (RulePattern RewritingVariableName))
applyRulesSequence sideCondition rules initial =
    applyWithFinalizer
        sideCondition
        ( finalizeSequence
            sideCondition
            RewriteRule
            (finalizeAppliedRule sideCondition)
        )
        rules
        initial

{- | Apply the given rewrite rules to the initial configuration in sequence.

See also: 'applyRewriteRulesParallel'
-}
applyRewriteRulesSequence ::
    forall simplifier.
    MonadSimplify simplifier =>
    -- | Configuration being rewritten
    Pattern RewritingVariableName ->
    -- | Rewrite rules
    [RewriteRule RewritingVariableName] ->
    simplifier (Results (RulePattern RewritingVariableName))
applyRewriteRulesSequence
    initialConfig
    (map getRewriteRule -> rules) =
        do
            let sideCondition =
                    SideCondition.cacheSimplifiedFunctions
                        (Pattern.toTermLike initialConfig)
            results <- applyRulesSequence sideCondition rules initialConfig
            assertFunctionLikeResults (term initialConfig) results
            return results

applyClaimsSequence ::
    forall goal simplifier.
    MonadSimplify simplifier =>
    UnifyingRuleWithRepresentation ClaimPattern goal =>
    (ClaimPattern -> goal) ->
    -- | Configuration being rewritten
    Pattern RewritingVariableName ->
    -- | Rewrite rules
    [ClaimPattern] ->
    simplifier (Results ClaimPattern)
applyClaimsSequence mkClaim initialConfig claims = do
    let sideCondition =
            SideCondition.cacheSimplifiedFunctions
                (Pattern.toTermLike initialConfig)
    results <-
        applyWithFinalizer
            sideCondition
            ( finalizeSequence
                sideCondition
                mkClaim
                (finalizeAppliedClaim sideCondition)
            )
            claims
            initialConfig
    assertFunctionLikeResults (term initialConfig) results
    return results
