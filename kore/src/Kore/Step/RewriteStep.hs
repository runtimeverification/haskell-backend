{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

Direct interface to rule application (step-wise execution).
See "Kore.Step" for the high-level strategy-based interface.
 -}

module Kore.Step.RewriteStep
    ( applyRewriteRulesParallel
    , withoutUnification
    , applyRewriteRulesSequence
    , applyClaimsSequence
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import qualified Control.Monad.State.Strict as State
import qualified Control.Monad.Trans.Class as Monad.Trans
import Data.Generics.Product
    ( field
    )
import qualified Data.Sequence as Seq

import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    )
import Kore.Attribute.SourceLocation
    ( SourceLocation
    )
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrCondition
    ( OrCondition
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Log.DebugAppliedRewriteRules
    ( debugAppliedRewriteRules
    )
import Kore.Log.ErrorRewritesInstantiation
    ( checkSubstitutionCoverage
    )
import Kore.Rewriting.RewritingVariable
import Kore.Step.AxiomPattern
    ( AxiomPattern
    )
import Kore.Step.ClaimPattern
    ( ClaimPattern (..)
    )
import qualified Kore.Step.ClaimPattern as Claim
import qualified Kore.Step.Remainder as Remainder
import qualified Kore.Step.Result as Result
import qualified Kore.Step.Result as Step
import Kore.Step.RulePattern
    ( RewriteRule (..)
    , RulePattern
    , mapRuleVariables
    )
import qualified Kore.Step.RulePattern as Rule
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , simplifyCondition
    )
import Kore.Step.Step
    ( Result
    , Results
    , UnificationProcedure (..)
    , UnifiedRule
    , applyInitialConditions
    , applyRemainder
    , assertFunctionLikeResults
    , unifyRules
    )
import Logic
    ( LogicT
    )
import qualified Logic

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
finalizeAppliedRule
    :: forall simplifier
    .  MonadSimplify simplifier
    => RulePattern RewritingVariableName
    -- ^ Applied rule
    -> OrCondition RewritingVariableName
    -- ^ Conditions of applied rule
    -> simplifier (OrPattern RewritingVariableName)
finalizeAppliedRule renamedRule appliedConditions =
    MultiOr.observeAllT
    $ finalizeAppliedRuleWorker =<< Logic.scatter appliedConditions
  where
    ruleRHS = Rule.rhs renamedRule
    finalizeAppliedRuleWorker appliedCondition = do
        -- Combine the initial conditions, the unification conditions, and the
        -- axiom ensures clause. The axiom requires clause is included by
        -- unifyRule.
        let
            avoidVars = freeVariables appliedCondition <> freeVariables ruleRHS
            finalPattern =
                Rule.topExistsToImplicitForall avoidVars ruleRHS
        constructConfiguration appliedCondition finalPattern

{- | Combine all the conditions to apply rule and construct the result.

@constructConfiguration@ combines:

* the applied condition (the initial condition, unification condition, and the
  rule's @requires@ clause), and
* the rule's @ensures@ clause

The parts of the applied condition were already combined by 'unifyRule'. First, the @ensures@ clause is simplified under the applied condition. Then, the conditions are conjoined and simplified again.

 -}
constructConfiguration
    :: MonadSimplify simplifier
    => Condition RewritingVariableName
    -> Pattern RewritingVariableName
    -> LogicT simplifier (Pattern RewritingVariableName)
constructConfiguration appliedCondition finalPattern = do
    let ensuresCondition = Pattern.withoutTerm finalPattern
    finalCondition <-
        do
            let sideCondition = SideCondition.fromCondition appliedCondition
            partial <- simplifyCondition sideCondition ensuresCondition
            -- TODO (thomas.tuegel): It should not be necessary to simplify
            -- after conjoining the conditions.
            simplifyCondition SideCondition.top (appliedCondition <> partial)
        & Logic.lowerLogicT
    -- Apply the normalized substitution to the right-hand side of the
    -- axiom.
    let
        Conditional { substitution } = finalCondition
        substitution' = Substitution.toMap substitution
        Conditional { term = finalTerm } = finalPattern
        finalTerm' = TermLike.substitute substitution' finalTerm
    -- TODO (thomas.tuegel): Should the final term be simplified after
    -- substitution?
    return (finalTerm' `Pattern.withCondition` finalCondition)

finalizeAppliedClaim
    :: forall simplifier
    .  MonadSimplify simplifier
    => ClaimPattern
    -- ^ Applied rule
    -> OrCondition RewritingVariableName
    -- ^ Conditions of applied rule
    -> simplifier (OrPattern RewritingVariableName)
finalizeAppliedClaim renamedRule appliedConditions =
    MultiOr.observeAllT
    $ finalizeAppliedRuleWorker =<< Logic.scatter appliedConditions
  where
    ClaimPattern { right } = renamedRule
    finalizeAppliedRuleWorker appliedCondition =
        Claim.assertRefreshed renamedRule $ do
            finalPattern <- Logic.scatter right
            -- Combine the initial conditions, the unification conditions, and
            -- the axiom ensures clause. The axiom requires clause is included
            -- by unifyRule.
            constructConfiguration appliedCondition finalPattern

type UnifyingRuleWithRepresentation representation rule =
    ( Rule.UnifyingRule representation
    , Rule.UnifyingRuleVariable representation ~ RewritingVariableName
    , Rule.UnifyingRule rule
    , Rule.UnifyingRuleVariable rule ~ RewritingVariableName
    , From rule (AxiomPattern RewritingVariableName)
    , From rule SourceLocation
    )

type FinalizeApplied rule simplifier =
    rule
    -> OrCondition RewritingVariableName
    -> LogicT simplifier (OrPattern RewritingVariableName)

finalizeRule
    :: UnifyingRuleWithRepresentation representation rule
    => MonadSimplify simplifier
    => (representation -> rule)
    -> FinalizeApplied representation simplifier
    -> FreeVariables RewritingVariableName
    -> Pattern RewritingVariableName
    -- ^ Initial conditions
    -> UnifiedRule representation
    -- ^ Rewriting axiom
    -> simplifier [Result representation]
finalizeRule toRule finalizeApplied initialVariables initial unifiedRule =
    Logic.observeAllT $ do
        let initialCondition = Conditional.withoutTerm initial
        let unificationCondition = Conditional.withoutTerm unifiedRule
        applied <- applyInitialConditions initialCondition unificationCondition
        checkSubstitutionCoverage initial (toRule <$> unifiedRule)
        let renamedRule = Conditional.term unifiedRule
        final <- finalizeApplied renamedRule applied
        let result =
                OrPattern.map (resetResultPattern initialVariables) final
        return Step.Result { appliedRule = unifiedRule, result }

-- | Finalizes a list of applied rules into 'Results'.
type Finalizer rule simplifier =
        MonadSimplify simplifier
    =>  FreeVariables RewritingVariableName
    ->  Pattern RewritingVariableName
    ->  [UnifiedRule rule]
    ->  simplifier (Results rule)

finalizeRulesParallel
    :: forall representation rule simplifier
    .  UnifyingRuleWithRepresentation representation rule
    => (representation -> rule)
    -> FinalizeApplied representation simplifier
    -> Finalizer representation simplifier
finalizeRulesParallel toRule finalizeApplied initialVariables initial unifiedRules = do
    results <-
        traverse (finalizeRule toRule finalizeApplied initialVariables initial) unifiedRules
        & fmap fold
    let unifications = MultiOr.make (Conditional.withoutTerm <$> unifiedRules)
        remainder = Condition.fromPredicate (Remainder.remainder' unifications)
    remainders <-
        applyRemainder initial remainder
        & Logic.observeAllT
        & fmap (fmap assertRemainderPattern >>> OrPattern.fromPatterns)
    return Step.Results
        { results = Seq.fromList results
        , remainders
        }

finalizeSequence
    :: forall representation rule simplifier
    .  UnifyingRuleWithRepresentation representation rule
    => (representation -> rule)
    -> FinalizeApplied representation simplifier
    -> Finalizer representation simplifier
finalizeSequence toRule finalizeApplied initialVariables initial unifiedRules = do
    (results, remainder) <-
        State.runStateT
            (traverse finalizeRuleSequence' unifiedRules)
            (Conditional.withoutTerm initial)
    remainders <-
        applyRemainder initial remainder
        & Logic.observeAllT
        & fmap (fmap assertRemainderPattern >>> OrPattern.fromPatterns)
    return Step.Results
        { results = Seq.fromList $ fold results
        , remainders
        }
  where
    initialTerm = Conditional.term initial
    finalizeRuleSequence' unifiedRule = do
        remainder <- State.get
        let remainderPattern = Conditional.withCondition initialTerm remainder
        results <-
            finalizeRule toRule finalizeApplied initialVariables remainderPattern unifiedRule
            & Monad.Trans.lift
        let unification = Conditional.withoutTerm unifiedRule
            remainder' =
                Condition.fromPredicate
                $ Remainder.remainder'
                $ MultiOr.singleton unification
        State.put (remainder `Conditional.andCondition` remainder')
        return results

applyWithFinalizer
    :: forall rule simplifier
    .  MonadSimplify simplifier
    => Rule.UnifyingRule rule
    => Rule.UnifyingRuleVariable rule ~ RewritingVariableName
    => From rule SourceLocation
    => Finalizer rule simplifier
    -> UnificationProcedure simplifier
    -> [rule]
    -- ^ Rewrite rules
    -> Pattern RewritingVariableName
    -- ^ Configuration being rewritten
    -> simplifier (Results rule)
applyWithFinalizer finalize unificationProcedure rules initial = do
    results <- unifyRules unificationProcedure initial rules
    debugAppliedRewriteRules initial (locations <$> results)
    let initialVariables = freeVariables initial
    finalize initialVariables initial results
  where
    locations = from @_ @SourceLocation . extract
{-# INLINE applyWithFinalizer #-}

{- | Apply the given rules to the initial configuration in parallel.

See also: 'applyRewriteRule'

 -}
applyRulesParallel
    :: forall simplifier
    .  MonadSimplify simplifier
    => UnificationProcedure simplifier
    -> [RulePattern RewritingVariableName]
    -- ^ Rewrite rules
    -> Pattern RewritingVariableName
    -- ^ Configuration being rewritten
    -> simplifier (Results (RulePattern RewritingVariableName))
applyRulesParallel = applyWithFinalizer (finalizeRulesParallel RewriteRule finalizeAppliedRule)

{- | Apply the given rewrite rules to the initial configuration in parallel.

See also: 'applyRewriteRule'

 -}
applyRewriteRulesParallel
    :: forall simplifier
    .  MonadSimplify simplifier
    => UnificationProcedure simplifier
    -> [RewriteRule RewritingVariableName]
    -- ^ Rewrite rules
    -> Pattern RewritingVariableName
    -- ^ Configuration being rewritten
    -> simplifier (Results (RulePattern RewritingVariableName))
applyRewriteRulesParallel
    unificationProcedure
    (map (mapRuleVariables resetRuleVariable . getRewriteRule) -> rules)
    (Pattern.mapVariables resetConfigVariable -> initial)
  = do
    results <- applyRulesParallel unificationProcedure rules initial
    assertFunctionLikeResults (term initial) results
    return
        $ results
        & field @"remainders"
            Lens.%~ MultiOr.map (Pattern.mapVariables resetConfigVariable)
        & (field @"results" . Lens.traverse . field @"result")
            Lens.%~ MultiOr.map (Pattern.mapVariables resetConfigVariable)


{- | Apply the given rewrite rules to the initial configuration in sequence.

See also: 'applyRewriteRule'

 -}
applyRulesSequence
    :: forall simplifier
    .  MonadSimplify simplifier
    => UnificationProcedure simplifier
    -> [RulePattern RewritingVariableName]
    -- ^ Rewrite rules
    -> Pattern RewritingVariableName
    -- ^ Configuration being rewritten
    -> simplifier (Results (RulePattern RewritingVariableName))
applyRulesSequence = applyWithFinalizer (finalizeSequence RewriteRule finalizeAppliedRule)

{- | Apply the given rewrite rules to the initial configuration in sequence.

See also: 'applyRewriteRulesParallel'

 -}
applyRewriteRulesSequence
    :: forall simplifier
    .  MonadSimplify simplifier
    => UnificationProcedure simplifier
    -> Pattern RewritingVariableName
    -- ^ Configuration being rewritten
    -> [RewriteRule RewritingVariableName]
    -- ^ Rewrite rules
    -> simplifier (Results (RulePattern RewritingVariableName))
applyRewriteRulesSequence
    unificationProcedure
    (Pattern.mapVariables resetConfigVariable -> initialConfig)
    (map (mapRuleVariables resetRuleVariable . getRewriteRule) -> rules)
  = do
    results <- applyRulesSequence unificationProcedure rules initialConfig
    assertFunctionLikeResults (term initialConfig) results
    return
        $ results
        & field @"remainders"
            Lens.%~
                MultiOr.map (Pattern.mapVariables resetConfigVariable)
        & (field @"results" . Lens.traverse . field @"result")
            Lens.%~
                MultiOr.map (Pattern.mapVariables resetConfigVariable)

applyClaimsSequence
    :: forall goal simplifier
    .  MonadSimplify simplifier
    => UnifyingRuleWithRepresentation ClaimPattern goal
    => (ClaimPattern -> goal)
    -> UnificationProcedure simplifier
    -> Pattern RewritingVariableName
    -- ^ Configuration being rewritten
    -> [ClaimPattern]
    -- ^ Rewrite rules
    -> simplifier (Results ClaimPattern)
applyClaimsSequence mkClaim unificationProcedure initialConfig claims = do
    results <-
        applyWithFinalizer
            (finalizeSequence mkClaim finalizeAppliedClaim)
            unificationProcedure
            claims
            initialConfig
    assertFunctionLikeResults (term initialConfig) results
    return results
