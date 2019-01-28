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
import           Kore.AST.Valid
import qualified Kore.Attribute.Axiom.Concrete as Axiom.Concrete
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateFalse, makeTruePredicate )
import           Kore.Step.AxiomPatterns
                 ( AxiomPatternAttributes (..), EqualityRule (EqualityRule),
                 RulePattern (..) )
import           Kore.Step.BaseStep
                 ( StepResult (StepResult), UnificationProcedure (..),
                 stepWithRule )
import           Kore.Step.BaseStep as StepResult
                 ( StepProof, StepResult (..) )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( bottom )
import           Kore.Step.Function.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
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
    => EqualityRule level
    -- ^ Axiom defining the current function.
    -> MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions in patterns
    -> CofreeF
        (Application level)
        (Valid (variable level) level)
        (StepPattern level variable)
    -- ^ The function on which to evaluate the current function.
    -> Simplifier
        (AttemptedAxiom level variable, SimplificationProof level)
ruleFunctionEvaluator
    (EqualityRule rule)
    tools
    substitutionSimplifier
    simplifier
    app@(_ :< Application _ c)
  | Axiom.Concrete.isConcrete (concrete $ attributes rule)
        && any (not . Pure.isConcrete) c
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
                    (OrOfExpandedPattern.make (map dropProof processedResults))
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
            (stepperConfiguration app)
            rule

    stepperConfiguration
        :: MetaOrObject level
        => CofreeF
            (Application level)
            (Valid (variable level) level)
            (StepPattern level variable)
        -> ExpandedPattern level variable
    stepperConfiguration (valid :< app') =
        Predicated
            { term = asPurePattern (valid :< ApplicationPattern app')
            , predicate = makeTruePredicate
            , substitution = mempty
            }

    processResult
        :: (StepResult level variable, StepProof level variable)
        -> Simplifier
            (ExpandedPattern level variable, SimplificationProof level)
    processResult
        (StepResult { rewrittenPattern = stepPattern }, _proof)
        -- TODO(virgil): ^^^ Also use the remainder.
      = do
        (   rewrittenPattern@Predicated { predicate = rewritingCondition }
            , _
            ) <-
                ExpandedPattern.simplifyPredicate
                    tools substitutionSimplifier simplifier stepPattern
        case rewritingCondition of
            PredicateFalse ->
                return (ExpandedPattern.bottom, SimplificationProof)
            _ -> return (rewrittenPattern, SimplificationProof)
