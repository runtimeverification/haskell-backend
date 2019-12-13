{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

Direct interface to rule application (step-wise execution).
See "Kore.Step" for the high-level strategy-based interface.
 -}

module Kore.Step.RewriteStep
    ( UnificationProcedure (..)
    , applyRewriteRulesParallel
    , Step.gatherResults
    , unwrapRule
    , withoutUnification
    , applyRewriteRulesSequence
    -- Below exports are just for tests
    , Results
    , Step.remainders
    , Step.result
    , Step.results
    , applyInitialConditions
    , unifyRule
    -- Below exports are just for EquationalStep
    -- TODO(traiansf): review and remove once EquationalStep is rewritten
    , Result
    , unifyRules
    , applyRemainder
    , toAxiomVariables
    , toConfigurationVariables
    , checkFunctionLike
    , checkSubstitutionCoverage
    , wouldNarrowWith
    , simplifyPredicate
    , assertFunctionLikeResults
    ) where

import qualified Control.Monad as Monad
import qualified Control.Monad.State.Strict as State
import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Branch
import qualified Kore.Attribute.Pattern.FreeVariables as FreeVariables
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
import Kore.Internal.TermLike as TermLike
import qualified Kore.Logger as Log
import Kore.Logger.DebugAppliedRule
import Kore.Step.AxiomPattern
import qualified Kore.Step.Remainder as Remainder
import qualified Kore.Step.Result as Result
import qualified Kore.Step.Result as Results
import qualified Kore.Step.Result as Step
import Kore.Step.RulePattern
    ( RewriteRule (..)
    , RulePattern
    )
import qualified Kore.Step.AxiomPattern as Rule
import qualified Kore.Step.RulePattern as Rule
import qualified Kore.Step.Simplification.Simplify as Simplifier
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
import qualified Kore.TopBottom as TopBottom
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unification.Unify
    ( MonadUnify
    , SimplifierVariable
    )
import qualified Kore.Unification.Unify as Monad.Unify
    ( gather
    , scatter
    )
import Kore.Unparser
import Kore.Variables.Target
    ( Target
    )
import qualified Kore.Variables.Target as Target
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    , foldMapVariable
    )

-- | Wraps functions such as 'unificationProcedure' and
-- 'Kore.Step.Axiom.Matcher.matchAsUnification' to be used in
-- 'stepWithRule'.

newtype UnificationProcedure =
    UnificationProcedure
        ( forall variable unifier
        .  (SimplifierVariable variable, MonadUnify unifier)
        => TermLike variable
        -> TermLike variable
        -> unifier (Condition variable)
        )

withoutUnification :: UnifiedRule variable rule -> rule
withoutUnification = Conditional.term

type Result variable rule =
    Step.Result (UnifiedRule (Target variable) rule) (Pattern variable)

type Results variable rule =
    Step.Results (UnifiedRule (Target variable) rule) (Pattern variable)

{- | Unwrap the variables in a 'RulePattern'.
 -}
unwrapRule
    :: Ord variable
    => RulePattern (Target variable) -> RulePattern variable
unwrapRule = Rule.mapVariables Target.unwrapVariable

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

{- | Attempt to unify a rule with the initial configuration.

The rule variables are renamed to avoid collision with the configuration. The
rule's 'RulePattern.requires' clause is combined with the unification
solution. The combined condition is simplified and checked for
satisfiability.

If any of these steps produces an error, then @unifyRule@ returns that error.

@unifyRule@ returns the renamed rule wrapped with the combined conditions on
unification. The substitution is not applied to the renamed rule.

 -}
unifyRule
    :: forall unifier variable rule
    .  SimplifierVariable variable
    => MonadUnify unifier
    => HasLeftPattern rule variable
    => HasRequiresPredicate rule variable
    => HasRefreshPattern rule variable
    => UnificationProcedure
    -> Pattern variable
    -- ^ Initial configuration
    -> rule variable
    -- ^ Rule
    -> unifier (UnifiedRule variable (rule variable))
unifyRule
    (UnificationProcedure unifyPatterns)
    initial@Conditional { term = initialTerm }
    rule
  = do
    -- Rename free axiom variables to avoid free variables from the initial
    -- configuration.
    let
        configVariables = freeVariables initial
        (_, rule') = refreshPattern configVariables rule
    -- Unify the left-hand side of the rule with the term of the initial
    -- configuration.
    let
        ruleLeft = leftPattern rule'
    unification <- unifyPatterns ruleLeft initialTerm
    -- Combine the unification solution with the rule's requirement clause,
    let
        ruleRequires = requiresPredicate rule'
        requires' = Condition.fromPredicate ruleRequires
    unification' <- simplifyPredicate (unification <> requires')
    return (rule' `Conditional.withCondition` unification')

unifyRules
    :: forall unifier variable rule
    .  MonadUnify unifier
    => HasLeftPattern rule (Target variable)
    => HasRefreshPattern rule (Target variable)
    => HasRequiresPredicate rule (Target variable)
    => UnificationProcedure
    -> Pattern (Target variable)
    -- ^ Initial configuration
    -> [rule (Target variable)]
    -- ^ Rule
    -> unifier [UnifiedRule (Target variable) (rule (Target variable))]
unifyRules unificationProcedure initial rules =
    Monad.Unify.gather $ do
        rule <- Monad.Unify.scatter rules
        unifyRule unificationProcedure initial rule

{- | Apply the initial conditions to the results of rule unification.

The rule is considered to apply if the result is not @\\bottom@.

 -}
applyInitialConditions
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => Condition variable
    -- ^ Initial conditions
    -> Condition variable
    -- ^ Unification conditions
    -> unifier (OrCondition variable)
    -- TODO(virgil): This should take advantage of the unifier's branching and
    -- not return an Or.
applyInitialConditions initial unification = do
    -- Combine the initial conditions and the unification conditions.
    -- The axiom requires clause is included in the unification conditions.
    applied <-
        Monad.liftM MultiOr.make
        $ Monad.Unify.gather
        $ simplifyPredicate (initial <> unification)
    evaluated <- SMT.Evaluator.filterMultiOr applied
    -- If 'evaluated' is \bottom, the rule is considered to not apply and
    -- no result is returned. If the result is \bottom after this check,
    -- then the rule is considered to apply with a \bottom result.
    TopBottom.guardAgainstBottom evaluated
    return evaluated

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
            preFinalCondition = appliedCondition <> ensuresCondition
        finalCondition <- simplifyPredicate preFinalCondition
        -- Apply the normalized substitution to the right-hand side of the
        -- axiom.
        let
            Conditional { substitution } = finalCondition
            substitution' = Substitution.toMap substitution
            Conditional { term = finalTerm} = finalPattern
            finalTerm' = TermLike.substitute substitution' finalTerm
        return finalCondition { Pattern.term = finalTerm' }

{- | Apply the remainder predicate to the given initial configuration.

 -}
applyRemainder
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => Pattern variable
    -- ^ Initial configuration
    -> Condition variable
    -- ^ Remainder
    -> unifier (Pattern variable)
applyRemainder initial remainder = do
    let final = initial `Conditional.andCondition` remainder
        finalCondition = Conditional.withoutTerm final
        Conditional { Conditional.term = finalTerm } = final
    normalizedCondition <- simplifyPredicate finalCondition
    return normalizedCondition { Conditional.term = finalTerm }

toAxiomVariables
    :: Ord variable
    => RulePattern variable
    -> RulePattern (Target variable)
toAxiomVariables = Rule.mapVariables Target.Target

toConfigurationVariables
    :: Ord variable
    => Pattern variable
    -> Pattern (Target variable)
toConfigurationVariables = Pattern.mapVariables Target.NonTarget

finalizeRule
    ::  ( SimplifierVariable variable
        , Log.WithLog Log.LogMessage unifier
        , MonadUnify unifier
        )
    => Pattern (Target variable)
    -- ^ Initial conditions
    -> UnifiedRule (Target variable) (RulePattern (Target variable))
    -- ^ Rewriting axiom
    -> unifier [Result variable (RulePattern (Target variable))]
    -- TODO (virgil): This is broken, it should take advantage of the unifier's
    -- branching and not return a list.
finalizeRule initial unifiedRule =
    Monad.Unify.gather $ do
        let initialCondition = Conditional.withoutTerm initial
        let unificationCondition = Conditional.withoutTerm unifiedRule
        applied <- applyInitialConditions initialCondition unificationCondition
        -- Log unifiedRule here since ^ guards against bottom
        debugAppliedRule unifiedRule
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
    -> unifier (Results variable (RulePattern (Target variable)))
finalizeRulesParallel initial unifiedRules = do
    results <- Foldable.fold <$> traverse (finalizeRule initial) unifiedRules
    let unifications = MultiOr.make (Conditional.withoutTerm <$> unifiedRules)
        remainder = Condition.fromPredicate (Remainder.remainder' unifications)
    remainders' <- Monad.Unify.gather $ applyRemainder initial remainder
    return Step.Results
        { results = Seq.fromList results
        , remainders =
            OrPattern.fromPatterns
            $ Pattern.mapVariables Target.unwrapVariable <$> remainders'
        }

assertFunctionLikeResults
    :: forall variable variable' rule m
    .  SimplifierVariable variable
    => SimplifierVariable variable'
    => Monad m
    => HasLeftPattern rule (Target variable')
    => Eq (rule (Target variable'))
    => TermLike variable
    -> Results variable' (rule (Target variable'))
    -> m ()
assertFunctionLikeResults termLike results =
    let appliedRules = Result.appliedRule <$> Results.results results
    in case checkFunctionLike appliedRules termLike of
        Left err -> error err
        _        -> return ()

finalizeRulesSequence
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => Pattern (Target variable)
    -> [UnifiedRule (Target variable) (RulePattern (Target variable))]
    -> unifier (Results variable (RulePattern (Target variable)))
finalizeRulesSequence initial unifiedRules
  = do
    (results, remainder) <-
        State.runStateT
            (traverse finalizeRuleSequence' unifiedRules)
            (Conditional.withoutTerm initial)
    remainders' <- Monad.Unify.gather $ applyRemainder initial remainder
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
            [Result variable (RulePattern (Target variable))]
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

checkFunctionLike
    :: InternalVariable variable
    => InternalVariable variable'
    => Foldable f
    => Eq (f (UnifiedRule variable' (rule variable')))
    => Monoid (f (UnifiedRule variable' (rule variable')))
    => HasLeftPattern rule variable'
    => f (UnifiedRule variable' (rule variable'))
    -> TermLike variable
    -> Either String ()
checkFunctionLike unifiedRules pat
  | unifiedRules == mempty = pure ()
  | TermLike.isFunctionPattern pat =
    Foldable.traverse_ checkFunctionLikeRule unifiedRules
  | otherwise = Left . show . Pretty.vsep $
    [ "Expected function-like term, but found:"
    , Pretty.indent 4 (unparse pat)
    ]
  where
    checkFunctionLikeRule Conditional { term }
      | TermLike.isFunctionPattern left = return ()
      | otherwise = Left . show . Pretty.vsep $
        [ "Expected function-like left-hand side of rule, but found:"
        , Pretty.indent 4 (unparse left)
        ]
      where
        left = leftPattern term

{- | Check that the final substitution covers the applied rule appropriately.

For normal execution, the final substitution should cover all the free
variables on the left-hand side of the applied rule; otherwise, we would
wrongly introduce existentially-quantified variables into the final
configuration. Failure of the coverage check indicates a problem with
unification, so in that case @checkSubstitutionCoverage@ throws
an error message with the axiom and the initial and final configurations.

For symbolic execution, we expect to replace symbolic variables with
more specific patterns (narrowing), so we just quantify the variables
we added to the result.

@checkSubstitutionCoverage@ calls @quantifyVariables@ to remove
the axiom variables from the substitution and unwrap all the 'Target's.
-}
checkSubstitutionCoverage
    :: forall variable rule unifier
    .  SimplifierVariable variable
    => MonadUnify unifier
    => HasLeftPattern rule (Target variable)
    => Pretty.Pretty (rule (Target variable))
    => Pattern (Target variable)
    -- ^ Initial configuration
    -> UnifiedRule (Target variable) (rule (Target variable))
    -- ^ Unified rule
    -> unifier ()
checkSubstitutionCoverage initial unified
  | isCoveringSubstitution || isSymbolic = return ()
  | otherwise =
    -- The substitution does not cover all the variables on the left-hand side
    -- of the rule *and* we did not generate a substitution for a symbolic
    -- initial configuration. This is a fatal error because it indicates
    -- something has gone horribly wrong.
    (error . show . Pretty.vsep)
        [ "While applying axiom:"
        , Pretty.indent 4 (Pretty.pretty axiom)
        , "from the initial configuration:"
        , Pretty.indent 4 (unparse initial)
        , "with the unifier:"
        , Pretty.indent 4 (unparse unifier)
        , "Failed substitution coverage check!"
        , "The substitution (above, in the unifier) \
          \did not cover the axiom variables:"
        , (Pretty.indent 4 . Pretty.sep)
            (unparse <$> Set.toAscList uncovered)
        , "in the left-hand side of the axiom."
        ]
  where
    Conditional { term = axiom } = unified
    unifier :: Pattern (Target variable)
    unifier = mkTop_ <$ Conditional.withoutTerm unified
    Conditional { substitution } = unified
    substitutionVariables = Map.keysSet (Substitution.toMap substitution)
    uncovered = wouldNarrowWith unified
    isCoveringSubstitution = Set.null uncovered
    isSymbolic =
        Foldable.any (foldMapVariable Target.isNonTarget)
            substitutionVariables

{- | The 'Set' of variables that would be introduced by narrowing.
 -}
-- TODO (thomas.tuegel): Unit tests
wouldNarrowWith
    :: Ord variable
    => HasLeftPattern rule variable
    => UnifiedRule variable (rule variable)
    -> Set (UnifiedVariable variable)
wouldNarrowWith unified =
    Set.difference leftAxiomVariables substitutionVariables
  where
    leftAxiomVariables =
        FreeVariables.getFreeVariables $ freeVariables leftAxiom
      where
        Conditional { term = axiom } = unified
        leftAxiom = leftPattern axiom
    Conditional { substitution } = unified
    substitutionVariables = Map.keysSet (Substitution.toMap substitution)

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
    -> unifier (Results variable (RulePattern (Target variable)))
applyRulesParallel
    unificationProcedure
    -- Wrap the rule and configuration so that unification prefers to substitute
    -- axiom variables.
    (map toAxiomVariables -> rules)
    initial
  = unifyRules unificationProcedure initial rules
    >>= finalizeRulesParallel initial

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
    -> unifier (Results variable (RulePattern (Target variable)))
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
    -> unifier (Results variable (RulePattern (Target variable)))
applyRulesSequence
    unificationProcedure
    initial
    -- Wrap the rules so that unification prefers to substitute
    -- axiom variables.
    (map toAxiomVariables -> rules)
  = unifyRules unificationProcedure initial rules
    >>= finalizeRulesSequence initial

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
    -> unifier (Results variable (RulePattern (Target variable)))
applyRewriteRulesSequence
    unificationProcedure
    (toConfigurationVariables -> initialConfig)
    (map getRewriteRule -> rules)
  = do
    results <- applyRulesSequence unificationProcedure initialConfig rules
    assertFunctionLikeResults (term initialConfig) results
    return results

simplifyPredicate
    :: forall unifier variable term
    .  SimplifierVariable variable
    => MonadUnify unifier
    => Conditional variable term
    -> unifier (Conditional variable term)
simplifyPredicate conditional =
    Branch.alternate (Simplifier.simplifyCondition conditional)
