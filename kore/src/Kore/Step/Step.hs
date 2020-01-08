{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

Unification of rules (used for stepping with rules or equations)

 -}
module Kore.Step.Step
    ( UnificationProcedure (..)
    , UnifiedRule
    , Result
    , Results
    , UnifyingRule (..)
    , unifyRules
    , unifyRule
    , applyInitialConditions
    , applyRemainder
    , simplifyPredicate
    , toAxiomVariables
    , toConfigurationVariables
    , toConfigurationVariablesCondition
    , unwrapRule
    , assertFunctionLikeResults
    , checkFunctionLike
    , checkSubstitutionCoverage
    , wouldNarrowWith
    -- Below exports are just for tests
    , Step.gatherResults
    , Step.remainders
    , Step.result
    , Step.results
    ) where

import qualified Control.Monad as Monad
import qualified Data.Foldable as Foldable
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Branch
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (..)
    )
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
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( andCondition
    , mapVariables
    )
import Kore.Internal.TermLike
    ( InternalVariable
    , SubstitutionVariable
    , TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Step.Result as Result
import qualified Kore.Step.Result as Results
import qualified Kore.Step.Result as Step
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
import Kore.Variables.Fresh
    ( Renaming
    )
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
        => SideCondition variable
        -> TermLike variable
        -> TermLike variable
        -> unifier (Condition variable)
        )

type UnifiedRule = Conditional

type Result rule variable =
    Step.Result
        (UnifiedRule (Target variable) (rule (Target variable)))
        (Pattern variable)

type Results rule variable =
    Step.Results
        (UnifiedRule (Target variable) (rule (Target variable)))
        (Pattern variable)

-- | A rule which can be unified against a configuration
class UnifyingRule rule where
    -- | The pattern used for matching/unifying the rule with the configuration.
    matchingPattern :: rule variable -> TermLike variable

    -- | The condition to be checked upon matching the rule
    precondition :: rule variable -> Predicate variable

    {-| Refresh the variables of a rule.
    The free variables of a rule are implicitly quantified, so they are
    renamed to avoid collision with any variables in the given set.
     -}
    refreshRule
        :: SubstitutionVariable variable
        => FreeVariables variable  -- ^ Variables to avoid
        -> rule variable
        -> (Renaming variable, rule variable)

    {-| Apply a given function to all variables in a rule. This is used for
    distinguishing rule variables from configuration variables.
    -}
    mapRuleVariables
        :: Ord variable2
        => (variable1 -> variable2)
        -> rule variable1
        -> rule variable2


-- |Unifies/matches a list a rules against a configuration. See 'unifyRule'.
unifyRules
    :: SimplifierVariable variable
    => MonadUnify unifier
    => UnifyingRule rule
    => UnificationProcedure
    -> SideCondition (Target variable)
    -> Pattern (Target variable)
    -- ^ Initial configuration
    -> [rule (Target variable)]
    -- ^ Rule
    -> unifier [UnifiedRule (Target variable) (rule (Target variable))]
unifyRules unificationProcedure sideCondition initial rules =
    Monad.Unify.gather $ do
        rule <- Monad.Unify.scatter rules
        unifyRule unificationProcedure sideCondition initial rule

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
    :: SimplifierVariable variable
    => MonadUnify unifier
    => UnifyingRule rule
    => UnificationProcedure
    -> SideCondition variable
    -- ^ Top level condition.
    -> Pattern variable
    -- ^ Initial configuration
    -> rule variable
    -- ^ Rule
    -> unifier (UnifiedRule variable (rule variable))
unifyRule
    (UnificationProcedure unifyPatterns)
    sideCondition
    initial
    rule
  = do
    let (initialTerm, initialCondition) = Pattern.splitTerm initial
        mergedSideCondition =
            sideCondition `SideCondition.andCondition` initialCondition
    -- Rename free axiom variables to avoid free variables from the initial
    -- configuration.
    let
        configVariables = TermLike.freeVariables initial
        (_, rule') = refreshRule configVariables rule
    -- Unify the left-hand side of the rule with the term of the initial
    -- configuration.
    let
        ruleLeft = matchingPattern rule'
    unification <- unifyPatterns mergedSideCondition ruleLeft initialTerm
    -- Combine the unification solution with the rule's requirement clause,
    let
        ruleRequires = precondition rule'
        requires' = Condition.fromPredicate ruleRequires
    unification' <-
        simplifyPredicate mergedSideCondition Nothing (unification <> requires')
    return (rule' `Conditional.withCondition` unification')

{- | The 'Set' of variables that would be introduced by narrowing.
 -}
-- TODO (thomas.tuegel): Unit tests
wouldNarrowWith
    :: Ord variable
    => UnifyingRule rule
    => UnifiedRule variable (rule variable)
    -> Set (UnifiedVariable variable)
wouldNarrowWith unified =
    Set.difference leftAxiomVariables substitutionVariables
  where
    leftAxiomVariables =
        FreeVariables.getFreeVariables $ TermLike.freeVariables leftAxiom
      where
        Conditional { term = axiom } = unified
        leftAxiom = matchingPattern axiom
    Conditional { substitution } = unified
    substitutionVariables = Map.keysSet (Substitution.toMap substitution)

-- |Renames variables to be distinguishable from those in configuration
toAxiomVariables
    :: Ord variable
    => UnifyingRule rule
    => rule variable
    -> rule (Target variable)
toAxiomVariables = mapRuleVariables Target.Target

{- | Unwrap the variables in a 'RulePattern'. Inverse of 'toAxiomVariables'.
 -}
unwrapRule
    :: Ord variable
    => UnifyingRule rule
    => rule (Target variable) -> rule variable
unwrapRule = mapRuleVariables Target.unwrapVariable

-- |Errors if configuration or matching pattern are not function-like
assertFunctionLikeResults
    :: SimplifierVariable variable
    => SimplifierVariable variable'
    => Monad m
    => UnifyingRule rule
    => Eq (rule (Target variable'))
    => TermLike variable
    -> Results rule variable'
    -> m ()
assertFunctionLikeResults termLike results =
    let appliedRules = Result.appliedRule <$> Results.results results
    in case checkFunctionLike appliedRules termLike of
        Left err -> error err
        _        -> return ()

-- |Checks whether configuration and matching pattern are function-like
checkFunctionLike
    :: InternalVariable variable
    => InternalVariable variable'
    => Foldable f
    => UnifyingRule rule
    => Eq (f (UnifiedRule variable' (rule variable')))
    => Monoid (f (UnifiedRule variable' (rule variable')))
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
        left = matchingPattern term

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
    :: forall variable unifier rule
    .  SimplifierVariable variable
    => MonadUnify unifier
    => UnifyingRule rule
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
    unifier = TermLike.mkTop_ <$ Conditional.withoutTerm unified
    Conditional { substitution } = unified
    substitutionVariables = Map.keysSet (Substitution.toMap substitution)
    uncovered = wouldNarrowWith unified
    isCoveringSubstitution = Set.null uncovered
    isSymbolic =
        Foldable.any (foldMapVariable Target.isNonTarget)
            substitutionVariables


{- | Apply the initial conditions to the results of rule unification.

The rule is considered to apply if the result is not @\\bottom@.

 -}
applyInitialConditions
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => SideCondition variable
    -- ^ Top-level conditions
    -> Maybe (Condition variable)
    -- ^ Initial conditions
    -> Condition variable
    -- ^ Unification conditions
    -> unifier (OrCondition variable)
    -- TODO(virgil): This should take advantage of the unifier's branching and
    -- not return an Or.
applyInitialConditions sideCondition initial unification = do
    -- Combine the initial conditions and the unification conditions.
    -- The axiom requires clause is included in the unification conditions.
    applied <-
        Monad.liftM MultiOr.make
        $ Monad.Unify.gather
        $ simplifyPredicate sideCondition initial unification
    evaluated <- SMT.Evaluator.filterMultiOr applied
    -- If 'evaluated' is \bottom, the rule is considered to not apply and
    -- no result is returned. If the result is \bottom after this check,
    -- then the rule is considered to apply with a \bottom result.
    TopBottom.guardAgainstBottom evaluated
    return evaluated

-- |Renames configuration variables to distinguish them from those in the rule.
toConfigurationVariables
    :: Ord variable
    => Pattern variable
    -> Pattern (Target variable)
toConfigurationVariables = Pattern.mapVariables Target.NonTarget

-- |Renames configuration variables to distinguish them from those in the rule.
toConfigurationVariablesCondition
    :: Ord variable
    => SideCondition variable
    -> SideCondition (Target variable)
toConfigurationVariablesCondition = SideCondition.mapVariables Target.NonTarget

{- | Apply the remainder predicate to the given initial configuration.

 -}
applyRemainder
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => SideCondition variable
    -- ^ Top level condition
    -> Pattern variable
    -- ^ Initial configuration
    -> Condition variable
    -- ^ Remainder
    -> unifier (Pattern variable)
applyRemainder sideCondition initial remainder = do
    let (initialTerm, initialCondition) = Pattern.splitTerm initial
    normalizedCondition <-
        simplifyPredicate sideCondition (Just initialCondition) remainder
    return normalizedCondition { Conditional.term = initialTerm }

-- | Simplifies the predicate obtained upon matching/unification.
simplifyPredicate
    :: forall unifier variable term
    .  SimplifierVariable variable
    => MonadUnify unifier
    => SideCondition variable
    -> Maybe (Condition variable)
    -> Conditional variable term
    -> unifier (Conditional variable term)
simplifyPredicate sideCondition (Just initialCondition) conditional = do
    partialResult <- Branch.alternate
        (Simplifier.simplifyCondition
            (sideCondition `SideCondition.andCondition` initialCondition)
            conditional
        )
    -- TODO (virgil): Consider using different simplifyPredicate implementations
    -- for rewrite rules and equational rules.
    -- Right now this double simplification both allows using the same code for
    -- both kinds of rules, and allows using the strongest background condition
    -- for simplifying the `conditional`. However, it's not obvious that
    -- using the strongest background condition actually helps in our
    -- use cases, so we may be able to do something better for equations.
    Branch.alternate
        (Simplifier.simplifyCondition
            sideCondition
            ( partialResult
            `Pattern.andCondition` initialCondition
            )
        )
simplifyPredicate sideCondition Nothing conditional =
    Branch.alternate
        (Simplifier.simplifyCondition
            sideCondition
            conditional
        )
