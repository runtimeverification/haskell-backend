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
    , assertFunctionLikeResults
    , recoveryFunctionLikeResults
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
import Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike as TermLike
import qualified Kore.Logger as Log
import Kore.Logger.DebugAppliedRule
import qualified Kore.Step.Remainder as Remainder
import qualified Kore.Step.Result as Result
import qualified Kore.Step.Result as Results
import qualified Kore.Step.Result as Step
import Kore.Step.Rule
    ( RewriteRule (..)
    , RulePattern (RulePattern, left, requires)
    )
import qualified Kore.Step.Rule as Rule
import qualified Kore.Step.Rule as RulePattern
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
    .  InternalVariable variable
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
    substitution' =
        Substitution.filter (foldMapVariable Target.isNonTarget)
            substitution

    configWithNewSubst :: Pattern (Target variable)
    configWithNewSubst = config { Pattern.substitution = substitution' }

    unwrappedConfig :: Pattern variable
    unwrappedConfig =
        Pattern.mapVariables Target.unwrapVariable configWithNewSubst

    targetVariables :: [ElementVariable variable]
    targetVariables =
        map (fmap Target.unwrapVariable)
        . filter (Target.isTarget . getElementVariable)
        . Pattern.freeElementVariables
        $ configWithNewSubst

    quantify :: TermLike variable -> ElementVariable variable -> TermLike variable
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
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => UnificationProcedure
    -> Pattern variable
    -- ^ Initial configuration
    -> RulePattern variable
    -- ^ Rule
    -> unifier (UnifiedRule variable)
unifyRule
    (UnificationProcedure unifyPatterns)
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
    -- Combine the unification solution with the rule's requirement clause,
    let
        RulePattern { requires = ruleRequires } = rule'
        requires' = Condition.fromPredicate ruleRequires
    unification' <- simplifyPredicate (unification <> requires')
    return (rule' `Conditional.withCondition` unification')

unifyRules
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => UnificationProcedure
    -> Pattern (Target variable)
    -- ^ Initial configuration
    -> [RulePattern (Target variable)]
    -- ^ Rule
    -> unifier [UnifiedRule (Target variable)]
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
    -- If 'applied' is \bottom, the rule is considered to not apply and
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
    finalizeAppliedRuleWorker appliedCondition = do
        -- Combine the initial conditions, the unification conditions, and the
        -- axiom ensures clause. The axiom requires clause is included by
        -- unifyRule.
        let
            RulePattern { ensures } = renamedRule
            ensuresCondition = Condition.fromPredicate ensures
            preFinalCondition = appliedCondition <> ensuresCondition
        finalCondition <- simplifyPredicate preFinalCondition
        -- Apply the normalized substitution to the right-hand side of the
        -- axiom.
        let
            Conditional { substitution } = finalCondition
            substitution' = Substitution.toMap substitution
            RulePattern { right = finalTerm } = renamedRule
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
toAxiomVariables = RulePattern.mapVariables Target.Target

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
    -> UnifiedRule (Target variable)
    -- ^ Rewriting axiom
    -> unifier [Result variable]
    -- TODO (virgil): This is broken, it should take advantage of the unifier's
    -- branching and not return a list.
finalizeRule initial unifiedRule =
    Log.withLogScope "finalizeRule" $ Monad.Unify.gather $ do
        let initialCondition = Conditional.withoutTerm initial
        let unificationCondition = Conditional.withoutTerm unifiedRule
        applied <- applyInitialConditions initialCondition unificationCondition
        -- Log unifiedRule here since ^ guards against bottom
        debugAppliedRule unifiedRule
        checkSubstitutionCoverage initial unifiedRule
        let renamedRule = Conditional.term unifiedRule
        final <- finalizeAppliedRule renamedRule applied
        let result = unwrapAndQuantifyConfiguration <$> final
        return Step.Result { appliedRule = unifiedRule, result }

finalizeRulesParallel
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => Pattern (Target variable)
    -> [UnifiedRule (Target variable)]
    -> unifier (Results variable)
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
    :: forall variable variable' m
    .  (SimplifierVariable variable, SimplifierVariable variable', Monad m)
    => TermLike variable
    -> Results variable'
    -> m ()
assertFunctionLikeResults termLike results =
    let appliedRules = fmap Result.appliedRule $ Results.results results
    in case checkFunctionLike appliedRules termLike of
        Left err -> error err
        _        -> return ()

{-
This is implementing the ideas from the [Applying axioms by matching]
(https://github.com/kframework/kore/blob/master/docs/2019-09-25-Applying-Axioms-By-Matching.md)
design doc, which checks that the unified lhs of the rule fully matches
(is equal to) the configuration term and that the lhs predicate is
implied by the configuration predicate.
-}
recoveryFunctionLikeResults
    :: forall variable simplifier
    .  SimplifierVariable variable
    => Simplifier.MonadSimplify simplifier
    => Pattern (Target variable)
    -> Results variable
    -> simplifier ()
recoveryFunctionLikeResults initial results = do
    let appliedRules = fmap Result.appliedRule $ Results.results results
    case checkFunctionLike appliedRules (Conditional.term initial) of
        Right _  -> return ()
        Left err -> moreChecksAfterError appliedRules err
  where
    moreChecksAfterError appliedRules err = do
        let
            appliedRule =
                case appliedRules of
                    rule Seq.:<| Seq.Empty -> rule
                    _ -> error $ show $ Pretty.vsep
                            [ "Expected singleton list of rules but found: "
                            , (Pretty.indent 4 . Pretty.vsep . Foldable.toList)
                                (Pretty.pretty . term <$> appliedRules)
                            , "This should be impossible, as simplifiers for \
                            \simplification are built from a single rule."
                            ]

            Conditional { term = ruleTerm, substitution = ruleSubstitution } =
                appliedRule
            RulePattern { left = alpha_t', requires = alpha_p'} = ruleTerm

            substitution' = Substitution.toMap ruleSubstitution

            alpha_t = TermLike.substitute substitution' alpha_t'
            alpha_p = Predicate.substitute substitution' alpha_p'
            phi_p = Conditional.predicate initial
            phi_t = Conditional.term initial

        res1 <- SMT.Evaluator.evaluate
                    $ Predicate.makeAndPredicate
                        phi_p
                        (Predicate.makeNotPredicate alpha_p)

        Monad.when (res1 /= Just False) $ error $ show $ Pretty.vsep
            [ "Couldn't recover simplification coverage error: "
            , Pretty.indent 4 (Pretty.pretty err)
            , "Configuration condition "
            , Pretty.indent 4 $ unparse phi_p
            , "doesn't imply rule condition "
            , Pretty.indent 4 $ unparse alpha_p
            ]
        let alpha_t_sorted = fullyOverrideSort' (termLikeSort phi_t) alpha_t
        Monad.when (phi_t /= alpha_t_sorted) $ error $ show $ Pretty.vsep
            [ "Couldn't recover simplification coverage error: "
            , Pretty.indent 4 (Pretty.pretty err)
            , "Rule lhs "
            , Pretty.indent 4 $ unparse alpha_t'
            , "doesn't match configuration"
            , Pretty.indent 4 $ unparse phi_t
            ]
        -- what we would like to check above is that phi_p -> phi_t = alpha_t,
        -- but that's hard to do for non-functional patterns,
        -- so we check for (syntactic) equality instead.
        return ()
    fullyOverrideSort' sort term
      | sort == termLikeSort term = term
      | otherwise = fullyOverrideSort sort term

finalizeRulesSequence
    :: forall unifier variable
    .  SimplifierVariable variable
    => MonadUnify unifier
    => Pattern (Target variable)
    -> [UnifiedRule (Target variable)]
    -> unifier (Results variable)
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
        :: UnifiedRule (Target variable)
        -> State.StateT (Condition (Target variable)) unifier [Result variable]
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
    ::  ( InternalVariable variable
        , InternalVariable variable'
        , Foldable f
        , Eq (f (UnifiedRule variable'))
        , Monoid (f (UnifiedRule variable'))
        )
    => f (UnifiedRule variable')
    -> TermLike variable
    -> Either String ()
checkFunctionLike unifiedRules term
  | unifiedRules == mempty = pure ()
  | TermLike.isFunctionPattern term =
    Foldable.traverse_ checkFunctionLikeRule unifiedRules
  | otherwise = Left . show . Pretty.vsep $
    [ "Expected function-like term, but found:"
    , Pretty.indent 4 (unparse term)
    ]
  where
    checkFunctionLikeRule Conditional { term = RulePattern { left } }
      | TermLike.isFunctionPattern left = return ()
      | otherwise = Left . show . Pretty.vsep $
        [ "Expected function-like left-hand side of rule, but found:"
        , Pretty.indent 4 (unparse left)
        ]

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
    :: forall variable unifier
    .  (SimplifierVariable variable, MonadUnify unifier)
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
    => UnifiedRule variable -> Set (UnifiedVariable variable)
wouldNarrowWith unified =
    Set.difference leftAxiomVariables substitutionVariables
  where
    leftAxiomVariables =
        FreeVariables.getFreeVariables $ TermLike.freeVariables leftAxiom
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
    .   ( SimplifierVariable variable
        , Log.WithLog Log.LogMessage unifier
        , MonadUnify unifier
        )
    => UnificationProcedure
    -> [RulePattern variable]
    -- ^ Rewrite rules
    -> Pattern (Target variable)
    -- ^ Configuration being rewritten
    -> unifier (Results variable)
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
    -> unifier (Results variable)
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
    -> unifier (Results variable)
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
    -> unifier (Results variable)
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
