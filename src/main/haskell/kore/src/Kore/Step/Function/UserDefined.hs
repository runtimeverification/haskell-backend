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
    , axiomFunctionEvaluator
    ) where

import Control.Monad.Except
       ( runExceptT )
import Data.Reflection

import           Kore.AST.Common
                 ( Application (..), Pattern (..), SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( asPurePattern )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateFalse, makeTruePredicate )
import           Kore.Step.BaseStep
                 ( AxiomPattern, StepResult (StepResult),
                 UnificationProcedure (..), stepWithAxiomForUnifier )
import           Kore.Step.BaseStep as StepResult
                 ( StepResult (..) )
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
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Fresh

{-| 'axiomFunctionEvaluator' evaluates a user-defined function. After
evaluating the function, it tries to re-evaluate all functions on the result.

The function is assumed to be defined through an axiom.
-}
axiomFunctionEvaluator
    ::  ( FreshVariable variable
        , Hashable variable
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , SortedVariable variable
        , Show (variable level)
        , ShowMetaOrObject variable
        )
    => AxiomPattern level
    -- ^ Axiom defining the current function.
    -> MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions in patterns
    -> Application level (StepPattern level variable)
    -- ^ The function on which to evaluate the current function.
    -> Simplifier (AttemptedFunction level variable, SimplificationProof level)
axiomFunctionEvaluator
    axiom
    tools
    substitutionSimplifier
    simplifier
    app
  = do
    result <- runExceptT stepResult
    case result of
        Left _ ->
            return (AttemptedFunction.NotApplicable, SimplificationProof)
        Right (StepResult { rewrittenPattern = stepPattern }, _proof) ->
            -- TODO(virgil): ^^^ Also use the remainder.
            do
                (   rewrittenPattern@Predicated
                        { predicate = rewritingCondition }
                    , _
                    ) <-
                        evaluatePredicate
                            tools substitutionSimplifier simplifier stepPattern
                case rewritingCondition of
                    PredicateFalse ->
                        return
                            ( AttemptedFunction.Applied
                                (OrOfExpandedPattern.make [])
                            , SimplificationProof
                            )
                    _ ->
                        reevaluateFunctions
                            tools
                            substitutionSimplifier
                            simplifier
                            rewrittenPattern
  where
    stepResult =
        stepWithAxiomForUnifier
            tools
            (UnificationProcedure matchAsUnification)
            substitutionSimplifier
            (stepperConfiguration app)
            axiom
    stepperConfiguration
        :: MetaOrObject level
        => Application level (StepPattern level variable)
        -> ExpandedPattern level variable
    stepperConfiguration app' =
        Predicated
            { term = asPurePattern $ ApplicationPattern app'
            , predicate = makeTruePredicate
            , substitution = []
            }

{-| 'reevaluateFunctions' re-evaluates functions after a user-defined function
was evaluated.
-}
reevaluateFunctions
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions in patterns.
    -> ExpandedPattern level variable
    -- ^ Function evaluation result.
    -> Simplifier (AttemptedFunction level variable, SimplificationProof level)
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
        ( AttemptedFunction.Applied evaluatedPatt
        , SimplificationProof
        )

evaluatePredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , Hashable variable
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
    (   Predicated
            { predicate = evaluatedPredicate
            , substitution = evaluatedSubstitution
            }
        , _proof
        ) <- give (symbolOrAliasSorts tools) $
             give tools $
                 Predicate.evaluate substitutionSimplifier simplifier predicate
    (   Predicated
            { predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , _proof
        ) <-
            mergePredicatesAndSubstitutions
                tools
                substitutionSimplifier
                [evaluatedPredicate]
                [substitution, evaluatedSubstitution]
    -- TODO(virgil): Do I need to re-evaluate the predicate?
    return
        ( Predicated
            { term = term
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , SimplificationProof
        )
