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

import Prelude.Kore

import qualified Control.Monad.State.Strict as State
import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.Sequence as Seq

import qualified Branch
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
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Log.DebugAppliedRewriteRules
    ( debugAppliedRewriteRules
    )
import Kore.Log.ErrorRewritesInstantiation
    ( checkSubstitutionCoverage
    )
import qualified Kore.Step.Remainder as Remainder
import qualified Kore.Step.Result as Result
import qualified Kore.Step.Result as Step
import Kore.Step.RulePattern
    ( RewriteRule (..)
    , RulePattern
    )
import qualified Kore.Step.RulePattern as Rule
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    )
import Kore.Step.Step
    ( Result
    , Results
    , UnificationProcedure (..)
    , UnifiedRule
    , applyInitialConditions
    , applyRemainder
    , assertFunctionLikeResults
    , simplifyPredicate
    , targetRuleVariables
    , toConfigurationVariables
    , unifyRules
    )
import Kore.Unification.Unify
    ( InternalVariable
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
    Pattern.mapVariables
        Target.unTargetElement
        Target.unTargetSet
        configWithNewSubst
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
    :: forall simplifier variable
    .  InternalVariable variable
    => MonadSimplify simplifier
    => RulePattern variable
    -- ^ Applied rule
    -> OrCondition variable
    -- ^ Conditions of applied rule
    -> simplifier (OrPattern variable)
finalizeAppliedRule renamedRule appliedConditions =
    MultiOr.gather
    $ finalizeAppliedRuleWorker =<< Branch.scatter appliedConditions
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
            & Branch.alternate
        -- Apply the normalized substitution to the right-hand side of the
        -- axiom.
        let
            Conditional { substitution } = finalCondition
            substitution' = Substitution.toMap substitution
            Conditional { term = finalTerm} = finalPattern
            finalTerm' = TermLike.substitute substitution' finalTerm
        return (finalTerm' `Pattern.withCondition` finalCondition)

finalizeRule
    ::  ( InternalVariable variable
        , MonadSimplify simplifier
        )
    => Pattern (Target variable)
    -- ^ Initial conditions
    -> UnifiedRule (Target variable) (RulePattern (Target variable))
    -- ^ Rewriting axiom
    -> simplifier [Result RulePattern variable]
finalizeRule initial unifiedRule =
    Branch.gather $ do
        let initialCondition = Conditional.withoutTerm initial
        let unificationCondition = Conditional.withoutTerm unifiedRule
        applied <- applyInitialConditions
            SideCondition.topTODO
            (Just initialCondition)
            unificationCondition
        checkSubstitutionCoverage initial (fmap RewriteRule unifiedRule)
        let renamedRule = Conditional.term unifiedRule
        final <- finalizeAppliedRule renamedRule applied
        let result = unwrapConfiguration <$> final
        return Step.Result { appliedRule = unifiedRule, result }

-- | Finalizes a list of applied rules into 'Results'.
type Finalizer simplifier variable
    =   InternalVariable variable
    =>  MonadSimplify simplifier
    =>  Pattern (Target variable)
    ->  [UnifiedRule (Target variable) (RulePattern (Target variable))]
    ->  simplifier (Results RulePattern variable)

finalizeRulesParallel :: forall simplifier variable. Finalizer simplifier variable
finalizeRulesParallel initial unifiedRules = do
    results <- Foldable.fold <$> traverse (finalizeRule initial) unifiedRules
    let unifications = MultiOr.make (Conditional.withoutTerm <$> unifiedRules)
        remainder = Condition.fromPredicate (Remainder.remainder' unifications)
    remainders' <-
        applyRemainder SideCondition.topTODO initial remainder
        & Branch.gather
    return Step.Results
        { results = Seq.fromList results
        , remainders =
            OrPattern.fromPatterns
            $ Pattern.mapVariables Target.unTargetElement Target.unTargetSet
            <$> remainders'
        }

finalizeRulesSequence :: forall simplifier variable. Finalizer simplifier variable
finalizeRulesSequence initial unifiedRules = do
    (results, remainder) <-
        State.runStateT
            (traverse finalizeRuleSequence' unifiedRules)
            (Conditional.withoutTerm initial)
    remainders' <-
        applyRemainder SideCondition.topTODO initial remainder
        & Branch.gather
    return Step.Results
        { results = Seq.fromList $ Foldable.fold results
        , remainders =
            OrPattern.fromPatterns
            $ Pattern.mapVariables Target.unTargetElement Target.unTargetSet
            <$> remainders'
        }
  where
    initialTerm = Conditional.term initial
    finalizeRuleSequence'
        :: UnifiedRule (Target variable) (RulePattern (Target variable))
        -> State.StateT
            (Condition (Target variable))
            simplifier
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

applyRulesWithFinalizer
    :: forall simplifier variable
    .  InternalVariable variable
    => MonadSimplify simplifier
    => Finalizer simplifier variable
    -> UnificationProcedure simplifier
    -> [RulePattern variable]
    -- ^ Rewrite rules
    -> Pattern (Target variable)
    -- ^ Configuration being rewritten
    -> simplifier (Results RulePattern variable)
applyRulesWithFinalizer finalize unificationProcedure rules initial = do
    let sideCondition = SideCondition.topTODO
        rules' = targetRuleVariables sideCondition initial <$> rules
    results <- unifyRules unificationProcedure sideCondition initial rules'
    debugAppliedRewriteRules initial results
    finalize initial results
{-# INLINE applyRulesWithFinalizer #-}

{- | Apply the given rules to the initial configuration in parallel.

See also: 'applyRewriteRule'

 -}
applyRulesParallel
    :: forall simplifier variable
    .  InternalVariable variable
    => MonadSimplify simplifier
    => UnificationProcedure simplifier
    -> [RulePattern variable]
    -- ^ Rewrite rules
    -> Pattern (Target variable)
    -- ^ Configuration being rewritten
    -> simplifier (Results RulePattern variable)
applyRulesParallel = applyRulesWithFinalizer finalizeRulesParallel

{- | Apply the given rewrite rules to the initial configuration in parallel.

See also: 'applyRewriteRule'

 -}
applyRewriteRulesParallel
    :: forall simplifier variable
    .  InternalVariable variable
    => MonadSimplify simplifier
    => UnificationProcedure simplifier
    -> [RewriteRule variable]
    -- ^ Rewrite rules
    -> Pattern variable
    -- ^ Configuration being rewritten
    -> simplifier (Results RulePattern variable)
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
    :: forall simplifier variable
    .  InternalVariable variable
    => MonadSimplify simplifier
    => UnificationProcedure simplifier
    -> [RulePattern variable]
    -- ^ Rewrite rules
    -> Pattern (Target variable)
    -- ^ Configuration being rewritten
    -> simplifier (Results RulePattern variable)
applyRulesSequence = applyRulesWithFinalizer finalizeRulesSequence

{- | Apply the given rewrite rules to the initial configuration in sequence.

See also: 'applyRewriteRulesParallel'

 -}
applyRewriteRulesSequence
    :: forall simplifier variable
    .  InternalVariable variable
    => MonadSimplify simplifier
    => UnificationProcedure simplifier
    -> Pattern variable
    -- ^ Configuration being rewritten
    -> [RewriteRule variable]
    -- ^ Rewrite rules
    -> simplifier (Results RulePattern variable)
applyRewriteRulesSequence
    unificationProcedure
    (toConfigurationVariables -> initialConfig)
    (map getRewriteRule -> rules)
  = do
    results <- applyRulesSequence unificationProcedure rules initialConfig
    assertFunctionLikeResults (term initialConfig) results
    return results
