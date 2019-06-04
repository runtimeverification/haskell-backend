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
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike as TermLike
import           Kore.Step.Axiom.Matcher
                 ( matchAsUnification )
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule), RulePattern (..) )
import qualified Kore.Step.Rule as RulePattern
import           Kore.Step.Simplification.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import           Kore.Step.Simplification.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import           Kore.Step.Simplification.Data
                 ( AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )
import qualified Kore.Step.Simplification.Pattern as Pattern
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
    ::  forall variable.
        ( FreshVariable variable
        , SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
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
    -> Simplifier (AttemptedAxiom variable)
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
    notApplicable :: Simplifier (AttemptedAxiom variable)
    notApplicable = return AttemptedAxiom.NotApplicable

    unificationProcedure :: UnificationProcedure
    unificationProcedure = UnificationProcedure matchAsUnification

    applyRule
        :: TermLike variable
        -> RulePattern Variable
        -> Simplifier
            (Either UnificationOrSubstitutionError [Step.Results variable])
    applyRule patt' rule' =
        Monad.Unify.runUnifier
        $ Step.applyRulesParallel
            unificationProcedure
            [RulePattern.mapVariables fromVariable rule']
            (Pattern.fromTermLike patt')

    simplifyOrPatterns
        :: [OrPattern variable] -> Simplifier (OrPattern variable)
    simplifyOrPatterns unsimplified =
        MultiOr.mergeAll
        <$> traverse
            simplifyPattern
            (MultiOr.extractPatterns (MultiOr.mergeAll unsimplified))

    simplifyPattern
        :: Pattern.Pattern variable
        -- ^ The condition to be evaluated.
        -> Simplifier (OrPattern variable)
    simplifyPattern config = do
        patterns <- BranchT.gather $ Pattern.simplifyPredicate config
        return (OrPattern.fromPatterns patterns)

    simplifyResults
        :: [Step.Results variable]
        -> Simplifier (AttemptedAxiomResults variable)
    simplifyResults stepResults = do
        results <- simplifyOrPatterns $ map Step.gatherResults stepResults
        remainders <- simplifyOrPatterns $ map Step.remainders stepResults
        return AttemptedAxiomResults { results, remainders }
