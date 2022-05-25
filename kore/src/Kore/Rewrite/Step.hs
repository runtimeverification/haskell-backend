{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause

Unification of rules (used for stepping with rules or equations)
-}
module Kore.Rewrite.Step (
    UnifiedRule,
    Result,
    Results,
    Renaming,
    UnifyingRule (..),
    InstantiationFailure (..),
    unifyRules,
    unifyRule,
    applyInitialConditions,
    applyRemainder,
    toConfigurationVariablesCondition,
    assertFunctionLikeResults,
    checkFunctionLike,
    wouldNarrowWith,

    -- * Re-exports
    mkRewritingPattern,
    -- Below exports are just for tests
    Step.gatherResults,
    Step.remainders,
    Step.result,
    Step.results,
) where

import Data.Map.Strict qualified as Map
import Data.Set (
    Set,
 )
import Data.Set qualified as Set
import Kore.Attribute.Pattern.FreeVariables qualified as FreeVariables
import Kore.Attribute.SourceLocation (
    SourceLocation,
 )
import Kore.Internal.Condition (
    Condition,
 )
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import Kore.Internal.Conditional qualified as Conditional
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.TermLike (
    InternalVariable,
    SomeVariableName,
    TermLike,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Log.DebugAttemptUnification
import Kore.Log.DebugAttemptedRewriteRules (
    debugAttemptedRewriteRule,
 )
import Kore.Rewrite.Result qualified as Result
import Kore.Rewrite.Result qualified as Results
import Kore.Rewrite.Result qualified as Step
import Kore.Rewrite.RewritingVariable
import Kore.Rewrite.SMT.Evaluator qualified as SMT.Evaluator
import Kore.Rewrite.UnifyingRule
import Kore.Simplify.Not qualified as Not
import Kore.Simplify.Simplify (
    MonadSimplify,
 )
import Kore.Simplify.Simplify qualified as Simplifier
import Kore.TopBottom qualified as TopBottom
import Kore.Unification.Procedure
import Kore.Unification.UnifierT (
    evalEnvUnifierT,
 )
import Kore.Unparser
import Kore.Variables.Target (
    Target,
 )
import Kore.Variables.Target qualified as Target
import Logic (
    LogicT,
 )
import Logic qualified
import Prelude.Kore
import Pretty qualified

type UnifiedRule rule = Conditional (UnifyingRuleVariable rule) rule

type Result rule =
    Step.Result
        (UnifiedRule rule)
        (Pattern (UnifyingRuleVariable rule))

type Results rule =
    Step.Results
        (UnifiedRule rule)
        (Pattern (UnifyingRuleVariable rule))

-- |Unifies/matches a list a rules against a configuration. See 'unifyRule'.
unifyRules ::
    MonadSimplify simplifier =>
    UnifyingRule rule =>
    UnifyingRuleVariable rule ~ RewritingVariableName =>
    From rule SourceLocation =>
    -- | SideCondition containing metadata
    SideCondition RewritingVariableName ->
    -- | Initial configuration
    Pattern RewritingVariableName ->
    -- | Rule
    [rule] ->
    simplifier [UnifiedRule rule]
unifyRules sideCondition initial rules =
    Logic.observeAllT $ do
        rule <- Logic.scatter rules
        unifyRule sideCondition initial rule

{- | Attempt to unify a rule with the initial configuration.

The rule variables are renamed to avoid collision with the configuration. The
rule's 'RulePattern.requires' clause is combined with the unification
solution. The combined condition is simplified and checked for
satisfiability.

If any of these steps produces an error, then @unifyRule@ returns that error.

@unifyRule@ returns the renamed rule wrapped with the combined conditions on
unification. The substitution is not applied to the renamed rule.
-}
unifyRule ::
    RewritingVariableName ~ UnifyingRuleVariable rule =>
    MonadSimplify simplifier =>
    UnifyingRule rule =>
    From rule SourceLocation =>
    -- | SideCondition containing metadata
    SideCondition RewritingVariableName ->
    -- | Initial configuration
    Pattern RewritingVariableName ->
    -- | Rule
    rule ->
    LogicT simplifier (UnifiedRule rule)
unifyRule sideCondition initial rule = do
    debugAttemptedRewriteRule initial (location rule)
    let (initialTerm, initialCondition) = Pattern.splitTerm initial
        sideCondition' =
            sideCondition
                & SideCondition.addConditionWithReplacements initialCondition
    -- Unify the left-hand side of the rule with the term of the initial
    -- configuration.
    let ruleLeft = matchingPattern rule
    debugAttemptUnificationStart (location rule)
    let unifComp =
            unificationProcedure sideCondition' initialTerm ruleLeft
                & evalEnvUnifierT Not.notSimplifier
    res <- Logic.observeAllT unifComp
    unification <-
        case res of
            [] -> do
                debugAttemptUnificationEnd (location rule)
                empty
            _ -> do
                debugAttemptUnificationEnd (location rule)
                Logic.scatter res
    -- Combine the unification solution with the rule's requirement clause,
    let ruleRequires = precondition rule
        requires' = Condition.fromPredicate ruleRequires
    unification' <-
        Simplifier.simplifyCondition
            sideCondition'
            (unification <> requires')
    return (rule `Conditional.withCondition` unification')
  where
    location = from @_ @SourceLocation

-- | The 'Set' of variables that would be introduced by narrowing.

-- TODO (thomas.tuegel): Unit tests
wouldNarrowWith ::
    forall rule variable.
    variable ~ UnifyingRuleVariable rule =>
    Ord variable =>
    UnifyingRule rule =>
    UnifiedRule rule ->
    Set (SomeVariableName variable)
wouldNarrowWith unified =
    Set.difference leftAxiomVariables substitutionVariables
  where
    leftAxiomVariables =
        TermLike.freeVariables leftAxiom
            & FreeVariables.toNames
      where
        Conditional{term = axiom} = unified
        leftAxiom = matchingPattern axiom
    Conditional{substitution} = unified
    substitutionVariables = Map.keysSet (Substitution.toMap substitution)

-- |Errors if configuration or matching pattern are not function-like
assertFunctionLikeResults ::
    variable ~ UnifyingRuleVariable rule =>
    InternalVariable variable =>
    Monad m =>
    UnifyingRule rule =>
    Eq rule =>
    TermLike variable ->
    Results rule ->
    m ()
assertFunctionLikeResults termLike results =
    let appliedRules = Result.appliedRule <$> Results.results results
     in case checkFunctionLike appliedRules termLike of
            Left err -> error err
            _ -> return ()

-- |Checks whether configuration and matching pattern are function-like
checkFunctionLike ::
    InternalVariable variable =>
    InternalVariable (UnifyingRuleVariable rule) =>
    Foldable f =>
    UnifyingRule rule =>
    Eq (f (UnifiedRule rule)) =>
    Monoid (f (UnifiedRule rule)) =>
    f (UnifiedRule rule) ->
    TermLike variable ->
    Either String ()
checkFunctionLike unifiedRules pat
    | unifiedRules == mempty = pure ()
    | TermLike.isFunctionPattern pat =
        traverse_ checkFunctionLikeRule unifiedRules
    | otherwise =
        Left . show . Pretty.vsep $
            [ "Expected function-like term, but found:"
            , Pretty.indent 4 (unparse pat)
            ]
  where
    checkFunctionLikeRule Conditional{term}
        | TermLike.isFunctionPattern left = return ()
        | otherwise =
            Left . show . Pretty.vsep $
                [ "Expected function-like left-hand side of rule, but found:"
                , Pretty.indent 4 (unparse left)
                ]
      where
        left = matchingPattern term

{- | Apply the initial conditions to the results of rule unification.

The rule is considered to apply if the result is not @\\bottom@.

@applyInitialConditions@ assumes that the unification solution includes the
@requires@ clause, and that their conjunction has already been simplified with
respect to the initial condition.
-}
applyInitialConditions ::
    forall simplifier.
    MonadSimplify simplifier =>
    -- | SideCondition containing metadata
    SideCondition RewritingVariableName ->
    -- | Initial conditions
    Condition RewritingVariableName ->
    -- | Unification conditions
    Condition RewritingVariableName ->
    LogicT simplifier (OrCondition RewritingVariableName)
-- TODO(virgil): This should take advantage of the LogicT and not return
-- an OrCondition.
applyInitialConditions sideCondition initial unification = do
    -- Combine the initial conditions and the unification conditions. The axiom
    -- requires clause is already included in the unification conditions, and
    -- the conjunction has already been simplified with respect to the initial
    -- conditions.
    applied <-
        -- Add the simplified unification solution to the initial conditions. We
        -- must preserve the initial conditions here, so it cannot be used as
        -- the side condition!
        Simplifier.simplifyCondition sideCondition (initial <> unification)
            & MultiOr.gather
    evaluated <- SMT.Evaluator.filterMultiOr applied
    -- If 'evaluated' is \bottom, the rule is considered to not apply and
    -- no result is returned. If the result is \bottom after this check,
    -- then the rule is considered to apply with a \bottom result.
    TopBottom.guardAgainstBottom evaluated
    return evaluated

-- |Renames configuration variables to distinguish them from those in the rule.
toConfigurationVariablesCondition ::
    InternalVariable variable =>
    SideCondition variable ->
    SideCondition (Target variable)
toConfigurationVariablesCondition =
    SideCondition.mapVariables Target.mkUnifiedNonTarget

-- | Apply the remainder predicate to the given initial configuration.
applyRemainder ::
    forall simplifier.
    MonadSimplify simplifier =>
    -- | SideCondition containing metadata
    SideCondition RewritingVariableName ->
    -- | Initial configuration
    Pattern RewritingVariableName ->
    -- | Remainder
    Condition RewritingVariableName ->
    LogicT simplifier (Pattern RewritingVariableName)
applyRemainder sideCondition initial remainder = do
    -- Simplify the remainder predicate under the initial conditions. We must
    -- ensure that functions in the remainder are evaluated using the top-level
    -- side conditions because we will not re-evaluate them after they are added
    -- to the top level.
    partial <-
        Simplifier.simplifyCondition
            ( sideCondition
                & SideCondition.addConditionWithReplacements
                    (Pattern.withoutTerm initial)
            )
            remainder
    -- Add the simplified remainder to the initial conditions. We must preserve
    -- the initial conditions here!
    Simplifier.simplifyCondition
        sideCondition
        (Pattern.andCondition initial partial)
        <&> Pattern.mapVariables resetConfigVariable
