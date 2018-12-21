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
import Data.Reflection

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateFalse, makeTruePredicate )
import           Kore.Step.AxiomPatterns
                 ( EqualityRule (EqualityRule) )
import           Kore.Step.BaseStep
                 ( StepResult (StepResult), UnificationProcedure (..),
                 stepWithRuleForUnifier )
import           Kore.Step.BaseStep as StepResult
                 ( StepProof, StepResult (..) )
import qualified Kore.Step.Condition.Evaluator as Predicate
                 ( evaluate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import           Kore.Step.Function.Data as AttemptedFunction
                 ( AttemptedFunction (..) )
import           Kore.Step.Function.Matcher
                 ( matchAsUnification )
import qualified Kore.Step.Merging.OrOfExpandedPattern as OrOfExpandedPattern
                 ( mergeWithPredicateSubstitution )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make, traverseWithPairs )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Unparser
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
        (Valid level)
        (StepPattern level variable)
    -- ^ The function on which to evaluate the current function.
    -> Simplifier
        [(AttemptedFunction level variable, SimplificationProof level)]
ruleFunctionEvaluator
    (EqualityRule rule)
    tools
    substitutionSimplifier
    simplifier
    app
  = do
    result <- runExceptT stepResult
    case result of
        Left _ ->
            return [(AttemptedFunction.NotApplicable, SimplificationProof)]
        Right results -> do
            processedResults <- mapM processResult results
            return (concat processedResults)
  where
    stepResult =
        stepWithRuleForUnifier
            tools
            (UnificationProcedure matchAsUnification)
            substitutionSimplifier
            (stepperConfiguration app)
            rule

    stepperConfiguration
        :: MetaOrObject level
        => CofreeF
            (Application level)
            (Valid level)
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
            [(AttemptedFunction level variable, SimplificationProof level)]
    processResult
        (StepResult { rewrittenPattern = stepPattern }, _proof)
        -- TODO(virgil): ^^^ Also use the remainder.
      = do
        (   rewrittenPattern@Predicated
                { predicate = rewritingCondition }
            , _
            ) <-
                evaluatePredicate
                    tools substitutionSimplifier simplifier stepPattern
        case rewritingCondition of
            PredicateFalse ->
                return
                    [   ( AttemptedFunction.Applied
                            (OrOfExpandedPattern.make [])
                        , SimplificationProof
                        )
                    ]
            _ ->
                reevaluateFunctions
                    tools
                    substitutionSimplifier
                    simplifier
                    rewrittenPattern


{-| 'reevaluateFunctions' re-evaluates functions after a user-defined function
was evaluated.
-}
reevaluateFunctions
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions in patterns.
    -> ExpandedPattern level variable
    -- ^ Function evaluation result.
    -> Simplifier
        [(AttemptedFunction level variable, SimplificationProof level)]
reevaluateFunctions
    tools
    substitutionSimplifier
    wrappedSimplifier@(StepPatternSimplifier simplifier)
    Predicated
        { term   = rewrittenPattern
        , predicate = rewritingCondition
        , substitution = rewrittenSubstitution
        }
  = do
    (pattOr , _proof) <-
        -- TODO(virgil): This call should be done in Evaluator.hs, but,
        -- for optimization purposes, it's done here. Make sure that
        -- this still makes sense after the evaluation code is fully
        -- optimized.
        simplifier substitutionSimplifier rewrittenPattern
    (mergedPatt, _proof) <-
        OrOfExpandedPattern.mergeWithPredicateSubstitution
            tools
            substitutionSimplifier
            wrappedSimplifier
            Predicated
                { term = ()
                , predicate = rewritingCondition
                , substitution = rewrittenSubstitution
                }
            pattOr
    (evaluatedPatt, _) <-
        OrOfExpandedPattern.traverseWithPairs
            (evaluatePredicate tools substitutionSimplifier wrappedSimplifier)
            mergedPatt
    return
        [( AttemptedFunction.Applied evaluatedPatt
        , SimplificationProof
        )]

evaluatePredicate
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions in a pattern.
    -> ExpandedPattern level variable
    -- ^ The condition to be evaluated.
    -> Simplifier (ExpandedPattern level variable, SimplificationProof level)
evaluatePredicate
    tools
    substitutionSimplifier
    simplifier
    Predicated {term, predicate, substitution}
  = do
    (evaluated, _proof) <-
        give tools
            $ Predicate.evaluate
                substitutionSimplifier
                simplifier
                predicate
    let Predicated { predicate = evaluatedPredicate } = evaluated
        Predicated { substitution = evaluatedSubstitution } = evaluated
    (merged, _proof) <-
        mergePredicatesAndSubstitutions
            tools
            substitutionSimplifier
            [evaluatedPredicate]
            [substitution, evaluatedSubstitution]
    let Predicated { predicate = mergedPredicate } = merged
        Predicated { substitution = mergedSubstitution } = merged
    -- TODO(virgil): Do I need to re-evaluate the predicate?
    return
        ( Predicated
            { term = term
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , SimplificationProof
        )
