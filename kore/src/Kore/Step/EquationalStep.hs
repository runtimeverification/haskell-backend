{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

Direct interface to equational rule application (step-wise execution).

 -}

module Kore.Step.EquationalStep
    ( UnificationProcedure (..)
    , Results
    , applyRulesSequence
    , isNarrowingResult
    , toConfigurationVariables
    , toConfigurationVariablesCondition
    , assertFunctionLikeResults
    , recoveryFunctionLikeResults
    ) where

import Prelude.Kore

import Control.Error
    ( MaybeT
    , maybeT
    )
import qualified Control.Monad as Monad
import qualified Control.Monad.State.Strict as State
import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Foldable as Foldable
import Data.Function
    ( (&)
    )
import qualified Data.List as List
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty

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
import Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Log.DebugAppliedRule
    ( debugAppliedRule
    )
import Kore.Step.Axiom.Matcher
    ( matchIncremental
    )
import Kore.Step.EqualityPattern
    ( EqualityPattern (..)
    )
import qualified Kore.Step.EqualityPattern as EqualityPattern
import qualified Kore.Step.Remainder as Remainder
import qualified Kore.Step.Result as Result
import qualified Kore.Step.Result as Results
import qualified Kore.Step.Result as Step
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
import Kore.Step.Step
    ( Result
    , Results
    , UnificationProcedure (..)
    , UnifiedRule
    , UnifyingRule
    , applyInitialConditions
    , applyRemainder
    , assertFunctionLikeResults
    , checkFunctionLike
    , checkSubstitutionCoverage
    , matchingPattern
    , precondition
    , simplifyPredicate
    , toConfigurationVariables
    , toConfigurationVariablesCondition
    , wouldNarrowWith
    )
import qualified Kore.Step.Step as EqualityPattern
    ( targetRuleVariables
    )
import Kore.Unification.UnifierT
    ( UnifierT
    )
import qualified Kore.Unification.UnifierT as Unifier
import Kore.Unification.Unify
    ( InternalVariable
    , MonadUnify
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
    ( foldMapVariable
    )
import qualified Log

{- | Is the result a symbolic rewrite, i.e. a narrowing result?

The result is narrowing if the unifier's substitution is missing any variable
from the left-hand side of the rule.

 -}
isNarrowingResult
    :: Ord variable
    => Result EqualityPattern variable
    -> Bool
isNarrowingResult Step.Result { appliedRule } =
    (not . Set.null) (wouldNarrowWith appliedRule)

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
        Pattern.mapVariables
            Target.unTargetElement
            Target.unTargetSet
            configWithNewSubst

    targetVariables :: [ElementVariable variable]
    targetVariables =
        map Target.unTargetElement
        . filter (Target.isTarget . getElementVariable)
        . Pattern.freeElementVariables
        $ configWithNewSubst

    quantify
        :: TermLike variable -> ElementVariable variable -> TermLike variable
    quantify = flip mkExists

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
    .  InternalVariable variable
    => MonadUnify unifier
    => SideCondition variable
    -- ^ Top level condition
    -> EqualityPattern variable
    -- ^ Applied rule
    -> OrCondition variable
    -- ^ Conditions of applied rule
    -> unifier (OrPattern variable)
finalizeAppliedRule sideCondition renamedRule appliedConditions =
    fmap OrPattern.fromPatterns . Monad.Unify.gather
    $ finalizeAppliedRuleWorker =<< Monad.Unify.scatter appliedConditions
  where
    finalizeAppliedRuleWorker appliedCondition = do
        -- Combine the initial conditions, the unification conditions, and the
        -- axiom ensures clause. The axiom requires clause is included by
        -- matchRule.
        let
            finalTerm = EqualityPattern.right renamedRule
            ensures = EqualityPattern.ensures renamedRule
            ensuresCondition = Condition.fromPredicate ensures
        finalCondition <- simplifyPredicate
            sideCondition
            (Just appliedCondition)
            ensuresCondition
        -- Apply the normalized substitution to the right-hand side of the
        -- axiom.
        let
            Conditional { substitution } = finalCondition
            substitution' = Substitution.toMap substitution
            finalTerm' = TermLike.substitute substitution' finalTerm
        return (finalTerm' `Pattern.withCondition` finalCondition)

finalizeRule
    ::  ( InternalVariable variable
        , Log.WithLog Log.LogMessage unifier
        , MonadUnify unifier
        )
    => SideCondition (Target variable)
    -- Top-level condition
    -> Pattern (Target variable)
    -- ^ Initial conditions
    -> UnifiedRule (Target variable) (EqualityPattern (Target variable))
    -- ^ Rewriting axiom
    -> unifier [Result EqualityPattern variable]
    -- TODO (virgil): This is broken, it should take advantage of the unifier's
    -- branching and not return a list.
finalizeRule sideCondition initial unifiedRule =
    Monad.Unify.gather $ do
        let initialCondition = Conditional.withoutTerm initial
        let unificationCondition = Conditional.withoutTerm unifiedRule
        applied <- applyInitialConditions
            sideCondition
            (Just initialCondition)
            unificationCondition
        -- Log unifiedRule here since ^ guards against bottom
        debugAppliedRule unifiedRule
        checkSubstitutionCoverage initial unifiedRule
        let renamedRule = Conditional.term unifiedRule
        final <- finalizeAppliedRule sideCondition renamedRule applied
        let result = unwrapAndQuantifyConfiguration <$> final
        return Step.Result { appliedRule = unifiedRule, result }

{-
This is implementing the ideas from the [Applying axioms by matching]
(https://github.com/kframework/kore/blob/master/docs/2019-09-25-Applying-Axioms-By-Matching.md)
design doc, which checks that the unified lhs of the rule fully matches
(is equal to) the configuration term and that the lhs predicate is
implied by the configuration predicate.
-}
recoveryFunctionLikeResults
    :: forall variable simplifier
    .  InternalVariable variable
    => Simplifier.MonadSimplify simplifier
    => Pattern (Target variable)
    -> Results EqualityPattern variable
    -> simplifier ()
recoveryFunctionLikeResults initial results = do
    let appliedRules = Result.appliedRule <$> Results.results results
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
            EqualityPattern { left = alpha_t', requires = alpha_p'} = ruleTerm

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
    fullyOverrideSort' sort term
      | sort == termLikeSort term = term
      | otherwise = fullyOverrideSort sort term

finalizeRulesSequence
    :: forall unifier variable
    .  InternalVariable variable
    => MonadUnify unifier
    => SideCondition (Target variable)
    -> Pattern (Target variable)
    -> [UnifiedRule (Target variable) (EqualityPattern (Target variable))]
    -> unifier (Results EqualityPattern variable)
finalizeRulesSequence sideCondition initial unifiedRules
  = do
    (results, remainder) <-
        State.runStateT
            (traverse finalizeRuleSequence' unifiedRules)
            (Conditional.withoutTerm initial)
    remainders' <- Monad.Unify.gather $
        applyRemainder sideCondition initial remainder
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
        :: UnifiedRule (Target variable) (EqualityPattern (Target variable))
        -> State.StateT
            (Condition (Target variable))
            unifier
            [Result EqualityPattern variable]
    finalizeRuleSequence' unifiedRule = do
        remainder <- State.get
        let remainderPattern = Conditional.withCondition initialTerm remainder
        results <- Monad.Trans.lift $
            finalizeRule sideCondition remainderPattern unifiedRule
        let unification = Conditional.withoutTerm unifiedRule
            remainder' =
                Condition.fromPredicate
                $ Remainder.remainder'
                $ MultiOr.singleton unification
        State.put (remainder `Conditional.andCondition` remainder')
        return results

{- | Apply the given rewrite rules to the initial configuration in sequence.

See also: 'applyRewriteRule'

 -}
applyRulesSequence
    ::  forall unifier variable
    .   ( InternalVariable variable
        , MonadUnify unifier
        )
    => SideCondition (Target variable)
    -> Pattern (Target variable)
    -- ^ Configuration being rewritten
    -> [EqualityPattern variable]
    -- ^ Rewrite rules
    -> unifier (Results EqualityPattern variable)
applyRulesSequence sideCondition initial rules =
    matchRules sideCondition initial rules'
    >>= finalizeRulesSequence sideCondition initial
  where
    rules' = EqualityPattern.targetRuleVariables sideCondition initial <$> rules

-- | Matches a list a rules against a configuration. See 'matchRule'.
matchRules
    :: InternalVariable variable
    => MonadUnify unifier
    => UnifyingRule rule
    => SideCondition (Target variable)
    -> Pattern (Target variable)
    -- ^ Initial configuration
    -> [rule (Target variable)]
    -- ^ Rule
    -> unifier [UnifiedRule (Target variable) (rule (Target variable))]
matchRules sideCondition initial rules =
    Monad.Unify.gather $ do
        rule <- Monad.Unify.scatter rules
        matchRule sideCondition initial rule
            & maybeT (couldNotMatch rule) Unifier.scatter
  where
    couldNotMatch rule =
        Unifier.explainAndReturnBottom
            "Could not match patterns"
            (matchingPattern rule)
            (term initial)

{- | Attempt to match a rule with the initial configuration.

The rule variables are renamed to avoid collision with the configuration. The
rule's 'RulePattern.requires' clause is combined with the unification
solution. The combined condition is simplified and checked for
satisfiability.

If any of these steps produces an error, then @matchRule@ returns that error.

@matchRule@ returns the renamed rule wrapped with the combined conditions on
unification. The substitution is not applied to the renamed rule.

 -}
matchRule
    :: InternalVariable variable
    => MonadSimplify simplifier
    => UnifyingRule rule
    => SideCondition variable
    -- ^ Top level condition.
    -> Pattern variable
    -- ^ Initial configuration
    -> rule variable
    -- ^ Rule
    -> MaybeT simplifier [UnifiedRule variable (rule variable)]
matchRule sideCondition initial rule = Unifier.maybeUnifierT $ do
    let (initialTerm, initialCondition) = Pattern.splitTerm initial
    -- Unify the left-hand side of the rule with the term of the initial
    -- configuration.
    let ruleLeft = matchingPattern rule
    unification <- matchIncremental ruleLeft initialTerm >>= maybe empty return
    -- Combine the unification solution with the rule's requirement clause,
    let requires = precondition rule
    unification' <-
        evaluateRequires sideCondition initialCondition unification requires
    return (rule `Conditional.withCondition` unification')

{- | Evaluate the pre-condition of a rule, subject to the given constraints.
 -}
evaluateRequires
    :: forall unifier variable
    .  InternalVariable variable
    => MonadUnify unifier
    => SideCondition variable
    -- ^ the side condition
    -> Condition variable
    -- ^ the initial condition, usually from simplifying children
    -> Condition variable
    -- ^ the solution used to instantiate the rule
    -> Predicate variable
    -- ^ the pre-condition itself (the @requires@ clause)
    -> unifier (Condition variable)
evaluateRequires side initial solution requires = do
    let requires' = solution <> Condition.fromPredicate requires
    requires'' <-
        simplifyCondition requires'
        -- disable function evaluation:
        & withoutAxioms
        -- do not propagate unification errors:
        & Unifier.maybeUnifierT
        -- if there is a unification error
        -- then continue with the original requirement,
        -- else continue with the partially-simplified requirement.
        & maybeT (return requires') Unifier.scatter
    simplifyCondition requires''
  where
    {- | Evaluate a 'Condition' simplifier without any axiom evaluation.

    The simplified status of the results is reset because any result may be
    further simplified when axiom evaluation is enabled.

     -}
    withoutAxioms
        :: UnifierT unifier (Condition variable)
        -> UnifierT unifier (Condition variable)
    withoutAxioms =
        fmap Condition.forgetSimplified
        . Simplifier.localSimplifierAxioms (const mempty)

    side' = SideCondition.andCondition side initial

    simplifyCondition
        :: forall unifier'
        .  MonadUnify unifier'
        => Condition variable
        -> unifier' (Condition variable)
    simplifyCondition = Branch.alternate . Simplifier.simplifyCondition side'
