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
    ) where

import qualified Control.Monad as Monad
import qualified Control.Monad.State.Strict as State
import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.Sequence as Seq

import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
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
    ( topTODO
    )
import Kore.Internal.TermLike as TermLike
import qualified Kore.Log as Log
import Kore.Log.DebugAppliedRewriteRules
    ( debugAppliedRewriteRules
    )
import qualified Kore.Step.Remainder as Remainder
import qualified Kore.Step.Result as Result
import qualified Kore.Step.Result as Step
import Kore.Step.RulePattern
    ( RewriteRule (..)
    , RulePattern
    )
import qualified Kore.Step.RulePattern as Rule
import Kore.Step.Step
    ( Result
    , Results
    , UnificationProcedure (..)
    , UnifiedRule
    , applyInitialConditions
    , applyRemainder
    , assertFunctionLikeResults
    , checkSubstitutionCoverage
    , simplifyPredicate
    , toAxiomVariables
    , toConfigurationVariables
    , unifyRules
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.Unify
    ( MonadUnify
    , SimplifierVariable
    )
import qualified Kore.Unification.Unify as Monad.Unify
    ( gather
    , scatter
    )
import Kore.Variables.Target
    ( Target
    )
import qualified Kore.Variables.Target as Target
import Kore.Variables.UnifiedVariable
    ( foldMapVariable
    )

withoutUnification :: UnifiedRule variable rule -> rule
withoutUnification = Conditional.term

{- | Remove axiom variables from the substitution and unwrap all variables.
 -}
unwrapConfiguration
    :: forall variable
    .  InternalVariable variable
    => Pattern (Target variable)
    -> Pattern variable
unwrapConfiguration config@Conditional { substitution } =
    Pattern.mapVariables Target.unwrapVariable configWithNewSubst
  where
    substitution' =
        Substitution.filter (foldMapVariable Target.isNonTarget)
            substitution

    configWithNewSubst :: Pattern (Target variable)
    configWithNewSubst = config { Pattern.substitution = substitution' }

{- | Produce the final configurations of an applied rule.

The rule's 'ensures' clause is applied to the conditions and normalized. The
substitution is applied to the right-hand side of the rule to produce the final
configurations.

Because the rule is known to apply, @finalizeAppliedRule@ always returns exactly
one branch.

See also: 'applyInitialConditions'

 -}
finalizeAppliedRule
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => RulePattern variable
    -- ^ Applied rule
    -> OrCondition variable
    -- ^ Conditions of applied rule
    -> unifier (OrPattern variable)
finalizeAppliedRule renamedRule appliedConditions =
    Monad.liftM OrPattern.fromPatterns . Monad.Unify.gather
    $ finalizeAppliedRuleWorker =<< Monad.Unify.scatter appliedConditions
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
            Conditional { predicate = ensures } = finalPattern
            ensuresCondition = Condition.fromPredicate ensures
        finalCondition <-
            simplifyPredicate
                SideCondition.topTODO (Just appliedCondition) ensuresCondition
        -- Apply the normalized substitution to the right-hand side of the
        -- axiom.
        let
            Conditional { substitution } = finalCondition
            substitution' = Substitution.toMap substitution
            Conditional { term = finalTerm} = finalPattern
            finalTerm' = TermLike.substitute substitution' finalTerm
        return (finalTerm' `Pattern.withCondition` finalCondition)

finalizeRule
    ::  ( SimplifierVariable variable
        , Log.WithLog Log.LogMessage unifier
        , MonadUnify unifier
        )
    => Pattern (Target variable)
    -- ^ Initial conditions
    -> UnifiedRule (Target variable) (RulePattern (Target variable))
    -- ^ Rewriting axiom
    -> unifier [Result RulePattern variable]
    -- TODO (virgil): This is broken, it should take advantage of the unifier's
    -- branching and not return a list.
finalizeRule initial unifiedRule =
    Monad.Unify.gather $ do
        let initialCondition = Conditional.withoutTerm initial
        let unificationCondition = Conditional.withoutTerm unifiedRule
        applied <- applyInitialConditions
            SideCondition.topTODO
            (Just initialCondition)
            unificationCondition
        checkSubstitutionCoverage initial unifiedRule
        let renamedRule = Conditional.term unifiedRule
        final <- finalizeAppliedRule renamedRule applied
        let result = unwrapConfiguration <$> final
        return Step.Result { appliedRule = unifiedRule, result }

finalizeRulesParallel
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => Pattern (Target variable)
    -> [UnifiedRule (Target variable) (RulePattern (Target variable))]
    -> unifier (Results RulePattern variable)
finalizeRulesParallel initial unifiedRules = do
    results <- Foldable.fold <$> traverse (finalizeRule initial) unifiedRules
    let unifications = MultiOr.make (Conditional.withoutTerm <$> unifiedRules)
        remainder = Condition.fromPredicate (Remainder.remainder' unifications)
    remainders' <- Monad.Unify.gather $
        applyRemainder SideCondition.topTODO initial remainder
    return Step.Results
        { results = Seq.fromList results
        , remainders =
            OrPattern.fromPatterns
            $ Pattern.mapVariables Target.unwrapVariable <$> remainders'
        }

finalizeRulesSequence
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => Pattern (Target variable)
    -> [UnifiedRule (Target variable) (RulePattern (Target variable))]
    -> unifier (Results RulePattern variable)
finalizeRulesSequence initial unifiedRules
  = do
    (results, remainder) <-
        State.runStateT
            (traverse finalizeRuleSequence' unifiedRules)
            (Conditional.withoutTerm initial)
    remainders' <- Monad.Unify.gather $
        applyRemainder SideCondition.topTODO initial remainder
    return Step.Results
        { results = Seq.fromList $ Foldable.fold results
        , remainders =
            OrPattern.fromPatterns
            $ Pattern.mapVariables Target.unwrapVariable <$> remainders'
        }
  where
    initialTerm = Conditional.term initial
    finalizeRuleSequence'
        :: UnifiedRule (Target variable) (RulePattern (Target variable))
        -> State.StateT
            (Condition (Target variable))
            unifier
            [Result RulePattern variable]
    finalizeRuleSequence' unifiedRule = do
        remainder <- State.get
        let remainderPattern = Conditional.withCondition initialTerm remainder
        results <- Monad.Trans.lift $ finalizeRule remainderPattern unifiedRule
        let unification = Conditional.withoutTerm unifiedRule
            remainder' =
                Condition.fromPredicate
                $ Remainder.remainder'
                $ MultiOr.singleton unification
        State.put (remainder `Conditional.andCondition` remainder')
        return results
{- | Apply the given rules to the initial configuration in parallel.

See also: 'applyRewriteRule'

 -}
applyRulesParallel
    ::  forall unifier variable
    .   ( SimplifierVariable variable
        , Log.WithLog Log.LogMessage unifier
        , MonadUnify unifier
        )
    => UnificationProcedure
    -> [RulePattern variable]
    -- ^ Rewrite rules
    -> Pattern (Target variable)
    -- ^ Configuration being rewritten
    -> unifier (Results RulePattern variable)
applyRulesParallel
    unificationProcedure
    -- Wrap the rule and configuration so that unification prefers to substitute
    -- axiom variables.
    (map toAxiomVariables -> rules)
    initial
  = do
      results <-
          unifyRules unificationProcedure SideCondition.topTODO initial rules
      debugAppliedRewriteRules initial results
      finalizeRulesParallel initial results

{- | Apply the given rewrite rules to the initial configuration in parallel.

See also: 'applyRewriteRule'

 -}
applyRewriteRulesParallel
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => UnificationProcedure
    -> [RewriteRule variable]
    -- ^ Rewrite rules
    -> Pattern variable
    -- ^ Configuration being rewritten
    -> unifier (Results RulePattern variable)
applyRewriteRulesParallel
    unificationProcedure
    (map getRewriteRule -> rules)
    (toConfigurationVariables -> initial)
  = do
    results <- applyRulesParallel unificationProcedure rules initial
    assertFunctionLikeResults (term initial) results
    return results


{- | Apply the given rewrite rules to the initial configuration in sequence.

See also: 'applyRewriteRule'

 -}
applyRulesSequence
    ::  forall unifier variable
    .   ( SimplifierVariable variable
        , Log.WithLog Log.LogMessage unifier
        , MonadUnify unifier
        )
    => UnificationProcedure
    -> Pattern (Target variable)
    -- ^ Configuration being rewritten
    -> [RulePattern variable]
    -- ^ Rewrite rules
    -> unifier (Results RulePattern variable)
applyRulesSequence
    unificationProcedure
    initial
    -- Wrap the rules so that unification prefers to substitute
    -- axiom variables.
    (map toAxiomVariables -> rules)
  = do
      results <-
          unifyRules unificationProcedure SideCondition.topTODO initial rules
      debugAppliedRewriteRules initial results
      finalizeRulesSequence initial results

{- | Apply the given rewrite rules to the initial configuration in sequence.

See also: 'applyRewriteRulesParallel'

 -}
applyRewriteRulesSequence
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => UnificationProcedure
    -> Pattern variable
    -- ^ Configuration being rewritten
    -> [RewriteRule variable]
    -- ^ Rewrite rules
    -> unifier (Results RulePattern variable)
applyRewriteRulesSequence
    unificationProcedure
    (toConfigurationVariables -> initialConfig)
    (map getRewriteRule -> rules)
  = do
    results <- applyRulesSequence unificationProcedure initialConfig rules
    assertFunctionLikeResults (term initialConfig) results
    return results
