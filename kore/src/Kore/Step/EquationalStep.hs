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
import qualified Control.Exception as Exception
import qualified Control.Monad as Monad
import qualified Data.Foldable as Foldable
import Data.Function
    ( (&)
    )
import qualified Data.List as List
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text.Prettyprint.Doc as Pretty

import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate as Predicate
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.Substitution
    ( Substitution
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Step.Axiom.Matcher
    ( matchIncremental
    )
import Kore.Step.EqualityPattern
    ( EqualityPattern (..)
    )
import qualified Kore.Step.EqualityPattern as EqualityPattern
import qualified Kore.Step.Result as Result
import qualified Kore.Step.Result as Results
import qualified Kore.Step.Result as Step
import qualified Kore.Step.Simplification.OrPattern as OrPattern
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
    , assertFunctionLikeResults
    , checkFunctionLike
    , matchingPattern
    , precondition
    , toConfigurationVariables
    , toConfigurationVariablesCondition
    , wouldNarrowWith
    )
import qualified Kore.Step.Step as EqualityPattern
    ( targetRuleVariables
    )
import Kore.Unification.Unify
    ( InternalVariable
    )
import Kore.Unparser
import Kore.Variables.Target
    ( Target
    )
import qualified Kore.Variables.Target as Target
import Kore.Variables.UnifiedVariable
    ( foldMapVariable
    )

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

{- | Apply the given rewrite rules to the initial configuration in sequence.

See also: 'applyRewriteRule'

 -}
applyRulesSequence
    ::  forall unifier variable
    .   ( InternalVariable variable
        , MonadSimplify unifier
        )
    => SideCondition (Target variable)
    -> Pattern (Target variable)
    -- ^ Configuration being rewritten
    -> [EqualityPattern variable]
    -- ^ Rewrite rules
    -> unifier (Results EqualityPattern variable)
applyRulesSequence sideCondition initial rules =
    Foldable.asum (matchRule sideCondition initial <$> rules')
        & maybeT noResults finalize
  where
    rules' = EqualityPattern.targetRuleVariables sideCondition initial <$> rules

    finalize
        :: UnifiedRule (Target variable) (EqualityPattern (Target variable))
        -> unifier (Results EqualityPattern variable)
    finalize unifiedRule = do
        let (renamedRule, solution) = Conditional.splitTerm unifiedRule
            Conditional { substitution } = solution
            substitution' = Substitution.toMap substitution
            term' =
                TermLike.substitute substitution'
                $ EqualityPattern.right renamedRule
            ensures =
                Condition.fromPredicate
                $ Predicate.substitute substitution'
                $ EqualityPattern.ensures renamedRule
        return Step.Results
            { remainders = mempty
            , results =
                Seq.singleton Step.Result
                    { appliedRule = unifiedRule
                    , result =
                        OrPattern.fromPattern
                        $ unwrapAndQuantifyConfiguration
                        $ Pattern.andCondition initial { term = term' } ensures
                    }
            }

    noResults :: unifier (Results EqualityPattern variable)
    noResults =
        return Step.Results
            { results = mempty
            , remainders =
                OrPattern.fromPattern
                $ Pattern.mapVariables
                    Target.unTargetElement
                    Target.unTargetSet
                    initial
            }

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
    => SideCondition (Target variable)
    -- ^ Top level condition.
    -> Pattern (Target variable)
    -- ^ Initial configuration
    -> rule (Target variable)
    -- ^ Rule
    ->  MaybeT simplifier
            (UnifiedRule (Target variable) (rule (Target variable)))
matchRule sideCondition initial rule = do
    let (initialTerm, initialCondition) = Pattern.splitTerm initial
    -- Match the left-hand side of the rule with the term of the initial
    -- configuration.
    let ruleLeft = matchingPattern rule
    solution <- matchIncremental ruleLeft initialTerm >>= maybe empty return
    -- Combine the unification solution with the rule's requirement clause,
    let requires = precondition rule
        mergedSideCondition =
            SideCondition.andCondition sideCondition initialCondition
    guardImplies mergedSideCondition solution requires
    return (rule `Conditional.withCondition` solution)

guardImplies
    :: InternalVariable variable
    => MonadSimplify simplifier
    => SideCondition (Target variable)
    -> Condition (Target variable)
    -> Predicate (Target variable)
    -> MaybeT simplifier ()
guardImplies sideCondition solution requires1 = do
    let Conditional { predicate = requires2, substitution } = solution
    Exception.assert (isMatchingSubstitution substitution) $ return ()
    let notRequires =
            Condition.fromPredicate
            $ Predicate.makeNotPredicate
            $ Predicate.makeAndPredicate requires1 requires2
        instantiation = Condition.fromSubstitution substitution
    notRequires' <-
        OrPattern.simplifyConditionsWithSmt sideCondition
        $ OrPattern.fromPattern . Pattern.fromCondition
        $ instantiation <> notRequires
    Monad.guard (isBottom notRequires')

isMatchingSubstitution :: Ord variable => Substitution (Target variable) -> Bool
isMatchingSubstitution =
    all (foldMapVariable Target.isTarget . fst) . Substitution.unwrap
