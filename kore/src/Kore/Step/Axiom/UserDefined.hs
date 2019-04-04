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
    ( StepPatternSimplifier
    , equalityRuleEvaluator
    ) where

import Control.Monad.Except
       ( runExceptT )

import           Kore.AST.Pure hiding
                 ( isConcrete )
import qualified Kore.AST.Pure as Pure
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Axiom.Concrete as Axiom.Concrete
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Step.Axiom.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import           Kore.Step.Axiom.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import           Kore.Step.Axiom.Data
                 ( AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Axiom.Matcher
                 ( matchAsUnification )
import           Kore.Step.Pattern
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
                 ( fromPurePattern )
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule), RulePattern (..) )
import qualified Kore.Step.Rule as RulePattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (..) )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import           Kore.Step.Step
                 ( UnificationProcedure (..) )
import qualified Kore.Step.Step as Step
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh

{-| Evaluates a pattern using user-defined axioms. After
evaluating the pattern, it tries to re-apply all axioms on the result.
-}
equalityRuleEvaluator
    ::  forall level variable.
        ( FreshVariable variable
        , SortedVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        )
    => EqualityRule level Variable
    -- ^ Axiom defining the current function.
    -> MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions in patterns
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> StepPattern level variable
    -- ^ The function on which to evaluate the current function.
    -> Simplifier
        (AttemptedAxiom level variable, SimplificationProof level)
equalityRuleEvaluator
    (EqualityRule rule)
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    patt
  -- TODO(traiansf): never apply smt-lemma axioms,
  -- neither as simplification rules nor as function definition rules
  | Axiom.Concrete.isConcrete (Attribute.concrete $ attributes rule)
  , not (Pure.isConcrete patt)
  = notApplicable
  | otherwise = do
    result <- runExceptT $ applyRule patt rule
    case result of
        Left _ ->
            notApplicable
        Right results ->
            (,)
                <$> (AttemptedAxiom.Applied <$> simplifyResults results)
                <*> pure SimplificationProof
  where
    notApplicable =
        return (AttemptedAxiom.NotApplicable, SimplificationProof)

    unificationProcedure = UnificationProcedure matchAsUnification

    applyRule patt' rule' =
        Step.applyRules
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            unificationProcedure
            [RulePattern.mapVariables fromVariable rule']
            (ExpandedPattern.fromPurePattern patt')

    simplifyOrOfExpandedPattern unsimplified =
        MultiOr.filterOr
        <$> traverse simplifyExpandedPattern unsimplified

    simplifyExpandedPattern config = do
        (config', _) <-
            ExpandedPattern.simplifyPredicate
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                config
        return config'

    simplifyResults
        :: Step.Results variable
        -> Simplifier (AttemptedAxiomResults Object variable)
    simplifyResults stepResults = do
        results <-
            simplifyOrOfExpandedPattern
            $ Step.result <$> Step.results stepResults
        remainders <- simplifyOrOfExpandedPattern $ Step.remainders stepResults
        return AttemptedAxiomResults { results, remainders }
