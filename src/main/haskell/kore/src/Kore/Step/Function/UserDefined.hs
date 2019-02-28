{-|
Module      : Kore.Step.Function.UserDefined
Description : Evaluates user-defined functions in a pattern.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Function.UserDefined
    ( StepPatternSimplifier
    , ruleFunctionEvaluator
    ) where

import Control.Monad.Except
       ( runExceptT )

import           Kore.AST.Pure hiding
                 ( isConcrete )
import qualified Kore.AST.Pure as Pure
import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Axiom.Concrete as Axiom.Concrete
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateFalse )
import           Kore.Step.AxiomPatterns
                 ( EqualityRule (EqualityRule), RulePattern (..) )
import qualified Kore.Step.AxiomPatterns as RulePattern
import           Kore.Step.BaseStep
                 ( StepResult (StepResult), UnificationProcedure (..),
                 stepWithRule )
import           Kore.Step.BaseStep as StepResult
                 ( StepProof, StepResult (..) )
import           Kore.Step.ExpandedPattern
                 ( Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( fromPurePattern )
import           Kore.Step.Function.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import           Kore.Step.Function.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import           Kore.Step.Function.Data
                 ( AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Function.Matcher
                 ( matchAsUnification )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (..) )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unparser
                 ( Unparse )
import           Kore.Variables.Fresh

{-| 'ruleFunctionEvaluator' evaluates a user-defined function. After
evaluating the function, it tries to re-evaluate all functions on the result.

The function is assumed to be defined through an axiom.
-}
ruleFunctionEvaluator
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
ruleFunctionEvaluator
    (EqualityRule rule)
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    patt
  | Axiom.Concrete.isConcrete (Attribute.concrete $ attributes rule)
  , not (Pure.isConcrete patt)
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
                { results = OrOfExpandedPattern.make
                    (case rewritingCondition of
                        PredicateFalse -> []
                        _ -> [rewrittenPattern]
                    )
                , remainders = OrOfExpandedPattern.make
                    (case remainderCondition of
                        PredicateFalse -> []
                        _ -> [rewrittenRemainder]
                    )
                }
            , SimplificationProof
            )
