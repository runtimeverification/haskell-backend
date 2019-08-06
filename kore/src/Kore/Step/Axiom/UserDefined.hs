{-|
Module      : Kore.Step.Axiom.UserDefined
Description : Evaluates user-defined functions in a pattern.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Axiom.UserDefined
    ( TermLikeSimplifier
    , equalityRuleEvaluator
    ) where

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Axiom.Concrete as Axiom.Concrete
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
                 ( TermLike )
import qualified Kore.Internal.TermLike as TermLike
import           Kore.Step.Axiom.Matcher
                 ( matchIncremental )
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule), RulePattern (..) )
import qualified Kore.Step.Rule as RulePattern
import           Kore.Step.Simplification.Data
                 ( AttemptedAxiom,
                 AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifierMap, MonadSimplify,
                 PredicateSimplifier, TermLikeSimplifier )
import qualified Kore.Step.Simplification.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import qualified Kore.Step.Simplification.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import qualified Kore.Step.Simplification.OrPattern as OrPattern
                 ( simplifyPredicatesWithSmt )
import           Kore.Step.Step
                 ( UnificationProcedure (..) )
import qualified Kore.Step.Step as Step
import           Kore.Unification.Error
                 ( UnificationOrSubstitutionError )
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh

{-| Evaluates a pattern using user-defined axioms. After
evaluating the pattern, it tries to re-apply all axioms on the result.
-}
equalityRuleEvaluator
    ::  forall variable simplifier
    .   ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        )
    => EqualityRule Variable
    -- ^ Axiom defining the current function.
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions in patterns
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -- ^ The function on which to evaluate the current function.
    -> simplifier (AttemptedAxiom variable)
equalityRuleEvaluator
    (EqualityRule rule)
    _substitutionSimplifier
    _simplifier
    _axiomIdToSimplifier
    patt
  -- TODO(traiansf): never apply smt-lemma axioms,
  -- neither as simplification rules nor as function definition rules
  | Axiom.Concrete.isConcrete (Attribute.concrete $ attributes rule)
  , not (TermLike.isConcrete patt)
  = notApplicable
  | otherwise = do
    result <- applyRule patt rule
    case result of
        Left _        -> notApplicable
        Right results -> AttemptedAxiom.Applied <$> simplifyResults results
  where
    notApplicable :: simplifier (AttemptedAxiom variable)
    notApplicable = return AttemptedAxiom.NotApplicable

    unificationProcedure :: UnificationProcedure
    unificationProcedure = UnificationProcedure matchIncremental

    applyRule
        :: TermLike variable
        -> RulePattern Variable
        -> simplifier
            (Either UnificationOrSubstitutionError [Step.Results variable])
    applyRule patt' rule' =
        Monad.Unify.runUnifierT
        $ Step.applyRulesParallel
            unificationProcedure
            [RulePattern.mapVariables fromVariable rule']
            (Pattern.fromTermLike patt')

    simplifyOrPatternsWithSmt
        :: [OrPattern variable] -> simplifier (OrPattern variable)
    simplifyOrPatternsWithSmt patterns = do
        simplified <- traverse OrPattern.simplifyPredicatesWithSmt patterns
        return (MultiOr.mergeAll simplified)

    simplifyResults
        :: [Step.Results variable]
        -> simplifier (AttemptedAxiomResults variable)
    simplifyResults stepResults = do
        results <-
            simplifyOrPatternsWithSmt
            $ map Step.gatherResults stepResults
        remainders <-
            simplifyOrPatternsWithSmt
            $ map Step.remainders stepResults
        return AttemptedAxiomResults { results, remainders }
