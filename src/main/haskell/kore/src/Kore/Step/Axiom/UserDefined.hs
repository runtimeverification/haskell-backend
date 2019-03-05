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
import qualified Kore.Attribute.Axiom.Concrete as Axiom.Concrete
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateFalse )
import           Kore.Step.Axiom.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import           Kore.Step.Axiom.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import           Kore.Step.Axiom.Data
                 ( AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Axiom.Matcher
                 ( matchAsUnification )
import           Kore.Step.AxiomPatterns
                 ( AxiomPatternAttributes (..), EqualityRule (EqualityRule),
                 RulePattern (..) )
import qualified Kore.Step.AxiomPatterns as RulePattern
import           Kore.Step.BaseStep
                 ( StepResult (StepResult), UnificationProcedure (..),
                 stepWithRule )
import           Kore.Step.BaseStep as StepResult
                 ( StepProof, StepResult (..) )
import           Kore.Step.Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
                 ( fromPurePattern )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( make )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (..) )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh

{-| Evaluates a pattern using user-defined axioms. After
evaluating the pattern, it tries to re-apply all axioms on the result.
-}
-- TODO: Rename to equalityRuleEvaluator
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
  | Axiom.Concrete.isConcrete (concrete $ attributes rule)
        && not (Pure.isConcrete patt)
  = notApplicable
  | otherwise = do
    result <- runExceptT stepResult
    case result of
        Left _ ->
            notApplicable
        Right results -> do
            processedResults <- mapM processResult results
            return
                ( AttemptedAxiom.Applied
                    (mconcat (map dropProof processedResults))
                , SimplificationProof
                )
  where
    notApplicable =
        return (AttemptedAxiom.NotApplicable, SimplificationProof)
    dropProof :: (a, SimplificationProof level) -> a
    dropProof = fst

    stepResult =
        stepWithRule
            tools
            (UnificationProcedure matchAsUnification)
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            (ExpandedPattern.fromPurePattern patt)
            (RulePattern.mapVariables fromVariable rule)

    processResult
        :: (StepResult level variable, StepProof level variable)
        -> Simplifier
            (AttemptedAxiomResults level variable, SimplificationProof level)
    processResult
        ( StepResult
            { rewrittenPattern = stepPattern, remainder = remainderPattern }
        , _proof
        )
      = do
        (   rewrittenPattern@Predicated { predicate = rewritingCondition }
            , _
            ) <-
                ExpandedPattern.simplifyPredicate
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    stepPattern
        (   rewrittenRemainder@Predicated { predicate = remainderCondition }
            , _
            ) <-
                ExpandedPattern.simplifyPredicate
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    remainderPattern
        return
            ( AttemptedAxiomResults
                { results = MultiOr.make
                    (case rewritingCondition of
                        PredicateFalse -> []
                        _ -> [rewrittenPattern]
                    )
                , remainders = MultiOr.make
                    (case remainderCondition of
                        PredicateFalse -> []
                        _ -> [rewrittenRemainder]
                    )
                }
            , SimplificationProof
            )
