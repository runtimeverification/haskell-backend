{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

Direct interface to rule application (step-wise execution).
See "Kore.Step" for the high-level strategy-based interface.

 -}

module Kore.Step.Step
    ( RulePattern
    , UnificationProcedure (..)
    , UnifiedRule
    , withoutUnification
    , Results
    , Step.remainders
    , Step.results
    , Result
    , isNarrowingResult
    , Step.appliedRule
    , Step.result
    , Step.gatherResults
    , Step.withoutRemainders
    , checkSubstitutionCoverage
    , unifyRule
    , unifyRules
    , applyInitialConditions
    , finalizeAppliedRule
    , unwrapRule
    , finalizeRulesParallel
    , applyRulesParallel
    , applyRewriteRulesParallel
    , finalizeRulesSequence
    , applyRulesSequence
    , applyRewriteRulesSequence
    , toConfigurationVariables
    , toAxiomVariables
    ) where

import qualified Control.Monad as Monad
import qualified Control.Monad.State.Strict as State
import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.Conditional
                 ( Conditional (Conditional) )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.OrPredicate
                 ( OrPredicate )
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.Predicate
                 ( Predicate )
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike as TermLike
import qualified Kore.Logger as Log
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Remainder as Remainder
import qualified Kore.Step.Result as Step
import           Kore.Step.Rule
                 ( RewriteRule (..), RulePattern (RulePattern) )
import qualified Kore.Step.Rule as Rule
import qualified Kore.Step.Rule as RulePattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Substitution as Substitution
import qualified Kore.TopBottom as TopBottom
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.Unify
                 ( MonadUnify )
import qualified Kore.Unification.Unify as Monad.Unify
                 ( gather, scatter )
import           Kore.Unparser
import           Kore.Variables.Fresh
import           Kore.Variables.Target
                 ( Target )
import qualified Kore.Variables.Target as Target

-- | Wraps functions such as 'unificationProcedure' and
-- 'Kore.Step.Axiom.Matcher.matchAsUnification' to be used in
-- 'stepWithRule'.
newtype UnificationProcedure =
    UnificationProcedure
        ( forall variable unifier
        .   ( SortedVariable variable
            , Ord variable
            , Show variable
            , Unparse variable
            , FreshVariable variable
            , MonadUnify unifier
            )
        => SmtMetadataTools StepperAttributes
        -> PredicateSimplifier
        -> TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> TermLike variable
        -> TermLike variable
        -> unifier (Predicate variable)
        )

{- | A @UnifiedRule@ has been renamed and unified with a configuration.

The rule's 'RulePattern.requires' clause is combined with the unification
solution and the renamed rule is wrapped with the combined condition.

 -}
type UnifiedRule variable = Conditional variable (RulePattern variable)

withoutUnification :: UnifiedRule variable -> RulePattern variable
withoutUnification = Conditional.term

type Result variable =
    Step.Result (UnifiedRule (Target variable)) (Pattern variable)

type Results variable =
    Step.Results (UnifiedRule (Target variable)) (Pattern variable)

{- | Is the result a symbolic rewrite, i.e. a narrowing result?

The result is narrowing if the unifier's substitution is missing any variable
from the left-hand side of the rule.

 -}
isNarrowingResult :: Ord variable => Result variable -> Bool
isNarrowingResult Step.Result { appliedRule } =
    (not . Set.null) (wouldNarrowWith appliedRule)

{- | Unwrap the variables in a 'RulePattern'.
 -}
unwrapRule
    :: Ord variable
    => RulePattern (Target variable) -> RulePattern variable
unwrapRule = Rule.mapVariables Target.unwrapVariable

{- | Remove axiom variables from the substitution and unwrap all variables.
 -}
unwrapAndQuantifyConfiguration
    :: forall variable
    .   ( Ord variable
        , Show variable
        , SortedVariable variable
        , Unparse variable
        )
    => Pattern (Target variable)
    -> Pattern variable
unwrapAndQuantifyConfiguration config@Conditional { substitution } =
    if List.null targetVariables
    then unwrappedConfig
    else
        Pattern.fromTermLike
            (List.foldl'
                quantify
                (Pattern.toTermLike unwrappedConfig)
                targetVariables
            )
  where
    substitution' = Substitution.filter Target.isNonTarget substitution

    configWithNewSubst :: Pattern (Target variable)
    configWithNewSubst = config { Pattern.substitution = substitution' }

    unwrappedConfig :: Pattern variable
    unwrappedConfig =
        Pattern.mapVariables Target.unwrapVariable configWithNewSubst

    targetVariables :: [variable]
    targetVariables =
        map Target.unwrapVariable
        $ filter Target.isTarget
        $ Set.toList
        $ Pattern.freeVariables configWithNewSubst

    quantify :: TermLike variable -> variable -> TermLike variable
    quantify = flip mkExists

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
    ::  forall unifier variable
    .   ( Ord     variable
        , Show    variable
        , Unparse variable
        , FreshVariable  variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> UnificationProcedure
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap

    -> Pattern variable
    -- ^ Initial configuration
    -> RulePattern variable
    -- ^ Rule
    -> unifier (UnifiedRule variable)
unifyRule
    metadataTools
    (UnificationProcedure unificationProcedure)
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers

    initial@Conditional { term = initialTerm }
    rule
  = do
    -- Rename free axiom variables to avoid free variables from the initial
    -- configuration.
    let
        configVariables = Pattern.freeVariables initial
        (_, rule') = RulePattern.refreshRulePattern configVariables rule
    -- Unify the left-hand side of the rule with the term of the initial
    -- configuration.
    let
        RulePattern { left = ruleLeft } = rule'
    unification <- unifyPatterns ruleLeft initialTerm
    -- Combine the unification solution with the rule's requirement clause.
    let
        RulePattern { requires = ruleRequires } = rule'
        requires' = Predicate.fromPredicate ruleRequires
    unification' <- normalize (unification <> requires')
    return (rule' `Conditional.withCondition` unification')
  where
    unifyPatterns
        :: TermLike variable
        -> TermLike variable
        -> unifier (Conditional variable ())
    unifyPatterns =
        unificationProcedure
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers
    normalize =
        Substitution.normalizeExcept
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers

unifyRules
    ::  forall unifier variable
    .   ( Ord     variable
        , Show    variable
        , Unparse variable
        , FreshVariable  variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -> UnificationProcedure

    -> Pattern (Target variable)
    -- ^ Initial configuration
    -> [RulePattern (Target variable)]
    -- ^ Rule
    -> unifier [UnifiedRule (Target variable)]
unifyRules
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers
    unificationProcedure

    initial
    rules
  =
    Monad.Unify.gather $ do
        rule <- Monad.Unify.scatter rules
        unified <- unifyRule' initial rule
        checkSubstitutionCoverage initial unified
        return unified
  where
    unifyRule' =
        unifyRule
            metadataTools
            unificationProcedure
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers

{- | Apply the initial conditions to the results of rule unification.

The rule is considered to apply if the result is not @\\bottom@.

 -}
applyInitialConditions
    ::  forall unifier variable
    .   ( Ord     variable
        , Show    variable
        , Unparse variable
        , FreshVariable  variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap

    -> Predicate variable
    -- ^ Initial conditions
    -> Predicate variable
    -- ^ Unification conditions
    -> unifier (OrPredicate variable)
    -- TODO(virgil): This should take advantage of the unifier's branching and
    -- not return an Or.
applyInitialConditions
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers

    initial
    unification
  = do
    -- Combine the initial conditions and the unification conditions.
    -- The axiom requires clause is included in the unification conditions.
    applied <-
        Monad.liftM MultiOr.make
        $ Monad.Unify.gather
        $ normalize (initial <> unification)
    -- If 'applied' is \bottom, the rule is considered to not apply and
    -- no result is returned. If the result is \bottom after this check,
    -- then the rule is considered to apply with a \bottom result.
    TopBottom.guardAgainstBottom applied
    return applied
  where
    normalize condition =
        Substitution.normalizeExcept
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers
            condition

{- | Produce the final configurations of an applied rule.

The rule's 'ensures' clause is applied to the conditions and normalized. The
substitution is applied to the right-hand side of the rule to produce the final
configurations.

Because the rule is known to apply, @finalizeAppliedRule@ always returns exactly
one branch.

See also: 'applyInitialConditions'

 -}
finalizeAppliedRule
    ::  forall unifier variable
    .   ( Ord     variable
        , Show    variable
        , Unparse variable
        , FreshVariable  variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap

    -> RulePattern variable
    -- ^ Applied rule
    -> OrPredicate variable
    -- ^ Conditions of applied rule
    -> unifier (OrPattern variable)
finalizeAppliedRule
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers

    renamedRule
    appliedConditions
  =
    Monad.liftM OrPattern.fromPatterns . Monad.Unify.gather
    $ finalizeAppliedRuleWorker =<< Monad.Unify.scatter appliedConditions
  where
    finalizeAppliedRuleWorker appliedCondition = do
        -- Combine the initial conditions, the unification conditions, and the
        -- axiom ensures clause. The axiom requires clause is included by
        -- unifyRule.
        let
            RulePattern { ensures } = renamedRule
            ensuresCondition = Predicate.fromPredicate ensures
        finalCondition <- normalize (appliedCondition <> ensuresCondition)
        -- Apply the normalized substitution to the right-hand side of the
        -- axiom.
        let
            Conditional { substitution } = finalCondition
            substitution' = Substitution.toMap substitution
            RulePattern { right = finalTerm } = renamedRule
            finalTerm' = TermLike.substitute substitution' finalTerm
        return finalCondition { Pattern.term = finalTerm' }

    normalize condition =
        Substitution.normalizeExcept
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers
            condition

{- | Apply the remainder predicate to the given initial configuration.

 -}
applyRemainder
    ::  forall unifier variable
    .   ( Ord     variable
        , Show    variable
        , Unparse variable
        , FreshVariable  variable
        , SortedVariable variable
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap

    -> Pattern variable
    -- ^ Initial configuration
    -> Predicate variable
    -- ^ Remainder
    -> unifier (Pattern variable)
applyRemainder
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers

    initial
    remainder
  = do
    let final = initial `Conditional.andCondition` remainder
        finalCondition = Conditional.withoutTerm final
        Conditional { Conditional.term = finalTerm } = final
    normalizedCondition <- normalize finalCondition
    let normalized = normalizedCondition { Conditional.term = finalTerm }
    return normalized
  where
    normalize condition =
        Substitution.normalizeExcept
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers
            condition

toAxiomVariables
    :: Ord variable
    => RulePattern variable
    -> RulePattern (Target variable)
toAxiomVariables = RulePattern.mapVariables Target.Target

toConfigurationVariables
    :: Ord variable
    => Pattern variable
    -> Pattern (Target variable)
toConfigurationVariables = Pattern.mapVariables Target.NonTarget

finalizeRule
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        , Log.WithLog Log.LogMessage unifier
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions

    -> Predicate (Target variable)
    -- ^ Initial conditions
    -> UnifiedRule (Target variable)
    -- ^ Rewriting axiom
    -> unifier [Result variable]
    -- TODO (virgil): This is broken, it should take advantage of the unifier's
    -- branching and not return a list.
finalizeRule
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers

    initialCondition
    unifiedRule
  = Log.withLogScope "finalizeRule" $ Monad.Unify.gather $ do
    let unificationCondition = Conditional.withoutTerm unifiedRule
    applied <- applyInitialConditions' initialCondition unificationCondition
    let renamedRule = Conditional.term unifiedRule
    final <- finalizeAppliedRule' renamedRule applied
    let result = unwrapAndQuantifyConfiguration <$> final
    return Step.Result { appliedRule = unifiedRule, result }
  where
    applyInitialConditions' =
        applyInitialConditions
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers
    finalizeAppliedRule' =
        finalizeAppliedRule
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers

finalizeRulesParallel
    ::  forall unifier variable
    .   ( Ord     variable
        , Show    variable
        , Unparse variable
        , FreshVariable  variable
        , SortedVariable variable
        , MonadUnify unifier
        , Log.WithLog Log.LogMessage unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap

    -> Pattern (Target variable)
    -> [UnifiedRule (Target variable)]
    -> unifier (Results variable)
finalizeRulesParallel
    metadataTools
    predicateSimplifier
    termSimplifier
    axiomSimplifiers

    initial
    unifiedRules
  = do
    let initialCondition = Conditional.withoutTerm initial
    results <-
        Foldable.fold <$> traverse (finalizeRule' initialCondition) unifiedRules
    let unifications = MultiOr.make (Conditional.withoutTerm <$> unifiedRules)
        remainder = Predicate.fromPredicate (Remainder.remainder' unifications)
    remainders' <- Monad.Unify.gather $ applyRemainder' initial remainder
    return Step.Results
        { results = Seq.fromList results
        , remainders =
            OrPattern.fromPatterns
            $ Pattern.mapVariables Target.unwrapVariable <$> remainders'
        }
  where
    finalizeRule' =
        finalizeRule
            metadataTools
            predicateSimplifier
            termSimplifier
            axiomSimplifiers
    applyRemainder' =
        applyRemainder
            metadataTools
            predicateSimplifier
            termSimplifier
            axiomSimplifiers

finalizeRulesSequence
    ::  forall unifier variable
    .   ( Ord     variable
        , Show    variable
        , Unparse variable
        , FreshVariable  variable
        , SortedVariable variable
        , MonadUnify unifier
        , Log.WithLog Log.LogMessage unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap

    -> Pattern (Target variable)
    -> [UnifiedRule (Target variable)]
    -> unifier (Results variable)
finalizeRulesSequence
    metadataTools
    predicateSimplifier
    termSimplifier
    axiomSimplifiers

    initial
    unifiedRules
  = do
    (results, remainder) <-
        State.runStateT
            (traverse finalizeRuleSequence' unifiedRules)
            (Conditional.withoutTerm initial)
    remainders' <- Monad.Unify.gather $ applyRemainder' initial remainder
    return Step.Results
        { results = Seq.fromList $ Foldable.fold results
        , remainders =
            OrPattern.fromPatterns
            $ Pattern.mapVariables Target.unwrapVariable <$> remainders'
        }
  where
    finalizeRuleSequence'
        :: UnifiedRule (Target variable)
        -> State.StateT (Predicate (Target variable)) unifier [Result variable]
    finalizeRuleSequence' unifiedRule = do
        remainder <- State.get
        results <- Monad.Trans.lift $ finalizeRule' remainder unifiedRule
        let unification = Conditional.withoutTerm unifiedRule
            remainder' =
                Predicate.fromPredicate
                $ Remainder.remainder'
                $ MultiOr.singleton unification
        State.put (remainder `Conditional.andCondition` remainder')
        return results
    finalizeRule' =
        finalizeRule
            metadataTools
            predicateSimplifier
            termSimplifier
            axiomSimplifiers
    applyRemainder' =
        applyRemainder
            metadataTools
            predicateSimplifier
            termSimplifier
            axiomSimplifiers

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
    ::  forall variable unifier
    .   ( SortedVariable variable
        , Ord     variable
        , Show    variable
        , Unparse variable
        , MonadUnify unifier
        )
    => Pattern (Target variable)
    -- ^ Initial configuration
    -> UnifiedRule (Target variable)
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
        , (Pretty.indent 4 . Pretty.sep) (unparse <$> Set.toAscList uncovered)
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
    isSymbolic = Foldable.any Target.isNonTarget substitutionVariables

{- | The 'Set' of variables that would be introduced by narrowing.
 -}
-- TODO (thomas.tuegel): Unit tests
wouldNarrowWith :: Ord variable => UnifiedRule variable -> Set variable
wouldNarrowWith unified =
    Set.difference leftAxiomVariables substitutionVariables
  where
    leftAxiomVariables =
        TermLike.freeVariables leftAxiom
      where
        Conditional { term = axiom } = unified
        RulePattern { left = leftAxiom } = axiom
    Conditional { substitution } = unified
    substitutionVariables = Map.keysSet (Substitution.toMap substitution)

{- | Apply the given rules to the initial configuration in parallel.

See also: 'applyRewriteRule'

 -}
applyRulesParallel
    ::  forall unifier variable
    .   ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        , Log.WithLog Log.LogMessage unifier
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> UnificationProcedure

    -> [RulePattern variable]
    -- ^ Rewrite rules
    -> Pattern variable
    -- ^ Configuration being rewritten
    -> unifier (Results variable)
applyRulesParallel
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers
    unificationProcedure

    -- Wrap the rule and configuration so that unification prefers to substitute
    -- axiom variables.
    (map toAxiomVariables -> rules)
    (toConfigurationVariables -> initial)
  =
    unifyRules' initial rules >>= finalizeRulesParallel' initial
  where
    unifyRules' =
        unifyRules
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers
            unificationProcedure
    finalizeRulesParallel' =
        finalizeRulesParallel
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers

{- | Apply the given rewrite rules to the initial configuration in parallel.

See also: 'applyRewriteRule'

 -}
applyRewriteRulesParallel
    ::  forall unifier variable
    .   ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        , Log.WithLog Log.LogMessage unifier
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> UnificationProcedure

    -> [RewriteRule variable]
    -- ^ Rewrite rules
    -> Pattern variable
    -- ^ Configuration being rewritten
    -> unifier (Results variable)
applyRewriteRulesParallel
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers
    unificationProcedure

    rewriteRules
  =
    applyRulesParallel
        metadataTools
        predicateSimplifier
        patternSimplifier
        axiomSimplifiers
        unificationProcedure
        (getRewriteRule <$> rewriteRules)

{- | Apply the given rewrite rules to the initial configuration in sequence.

See also: 'applyRewriteRule'

 -}
applyRulesSequence
    ::  forall unifier variable
    .   ( Ord     variable
        , Show    variable
        , Unparse variable
        , FreshVariable  variable
        , SortedVariable variable
        , Log.WithLog Log.LogMessage unifier
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> UnificationProcedure

    -> Pattern variable
    -- ^ Configuration being rewritten
    -> [RulePattern variable]
    -- ^ Rewrite rules
    -> unifier (Results variable)
applyRulesSequence
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers
    unificationProcedure

    -- Wrap the rule and configuration so that unification prefers to substitute
    -- axiom variables.
    (toConfigurationVariables -> initial)
    (map toAxiomVariables -> rules)
  =
    unifyRules' initial rules >>= finalizeRulesSequence' initial
  where
    unifyRules' =
        unifyRules
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers
            unificationProcedure
    finalizeRulesSequence' =
        finalizeRulesSequence
            metadataTools
            predicateSimplifier
            patternSimplifier
            axiomSimplifiers

{- | Apply the given rewrite rules to the initial configuration in sequence.

See also: 'applyRewriteRulesParallel'

 -}
applyRewriteRulesSequence
    ::  forall unifier variable
    .   ( Ord     variable
        , Show    variable
        , Unparse variable
        , FreshVariable  variable
        , SortedVariable variable
        , Log.WithLog Log.LogMessage unifier
        , MonadUnify unifier
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> UnificationProcedure

    -> Pattern variable
    -- ^ Configuration being rewritten
    -> [RewriteRule variable]
    -- ^ Rewrite rules
    -> unifier (Results variable)
applyRewriteRulesSequence
    metadataTools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers
    unificationProcedure

    initialConfig
    rewriteRules
  =
    applyRulesSequence
        metadataTools
        predicateSimplifier
        patternSimplifier
        axiomSimplifiers
        unificationProcedure
        initialConfig
        (getRewriteRule <$> rewriteRules)
