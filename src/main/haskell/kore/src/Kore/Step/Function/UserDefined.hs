{-|
Module      : Kore.Step.Function.UserDefined
Description : Evaluates user-defined functions in a pattern.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Function.UserDefined
    ( PureMLPatternSimplifier
    , axiomFunctionEvaluator
    ) where

import qualified Control.Monad.Except as Except
import           Data.Reflection
                 ( give )

import           Kore.AST.Common
                 ( Application (..), Pattern (..), SortedVariable, KoreDomain )
import           Kore.AST.MetaOrObject
                 ( Meta, MetaOrObject, Object )
import           Kore.AST.PureML
                 ( CommonPurePattern, PureMLPattern, asPurePattern )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( pattern PredicateFalse, makeTruePredicate )
import           Kore.Step.BaseStep
                 ( AxiomPattern, stepWithAxiom )
import qualified Kore.Step.Condition.Evaluator as Predicate
                 ( evaluate )
import           Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import           Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution (PredicateSubstitution) )
import           Kore.Step.Function.Data as AttemptedFunction
                 ( AttemptedFunction (..) )
import           Kore.Step.Function.Data
                 ( CommonAttemptedFunction )
import qualified Kore.Step.Merging.OrOfExpandedPattern as OrOfExpandedPattern
                 ( mergeWithPredicateSubstitution )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( make, traverseWithPairs )
import           Kore.Step.Simplification.Data
                 ( CommonPureMLPatternSimplifier, PureMLPatternSimplifier (..),
                   Simplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Int
                 ( IntVariable (..) )

{-| 'axiomFunctionEvaluator' evaluates a user-defined function. After
evaluating the function, it tries to re-evaluate all functions on the result.

The function is assumed to be defined through an axiom.
-}
axiomFunctionEvaluator
    ::  ( MetaOrObject level)
    => AxiomPattern level KoreDomain
    -- ^ Axiom defining the current function.
    -> MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> CommonPureMLPatternSimplifier level KoreDomain
    -- ^ Evaluates functions in patterns
    -> Application level (CommonPurePattern level KoreDomain)
    -- ^ The function on which to evaluate the current function.
    -> Simplifier (CommonAttemptedFunction level KoreDomain, ())
axiomFunctionEvaluator
    axiom
    tools
    simplifier
    app
  =
    case stepResult of
        Left _ ->
            return (AttemptedFunction.NotApplicable, ())
        Right stepPattern1 ->
            do
                (stepPattern, _) <- Except.lift stepPattern1
                (   rewrittenPattern@ExpandedPattern
                        { predicate = rewritingCondition }
                    , _
                    ) <- evaluatePredicate tools simplifier stepPattern
                case rewritingCondition of
                    PredicateFalse ->
                        return
                            ( AttemptedFunction.Applied
                                (OrOfExpandedPattern.make [])
                            , ()
                            )
                    _ ->
                        reevaluateFunctions
                            tools
                            simplifier
                            rewrittenPattern
  where
    stepResult =
        stepWithAxiom
            tools
            (stepperConfiguration app)
            axiom
    stepperConfiguration
        :: MetaOrObject level
        => Application level (PureMLPattern level domain variable)
        -> ExpandedPattern level domain variable
    stepperConfiguration app' =
        ExpandedPattern
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
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PureMLPatternSimplifier level domain variable
    -- ^ Evaluates functions in patterns.
    -> ExpandedPattern level domain variable
    -- ^ Function evaluation result.
    -> Simplifier (AttemptedFunction level domain variable, ())
reevaluateFunctions
    tools
    wrappedSimplifier@(PureMLPatternSimplifier simplifier)
    ExpandedPattern
        { term   = rewrittenPattern
        , predicate = rewritingCondition
        , substitution = rewrittenSubstitution
        }
  = do
    (pattOr , ()) <-
        -- TODO(virgil): This call should be done in Evaluator.hs, but,
        -- for optimization purposes, it's done here. Make sure that
        -- this still makes sense after the evaluation code is fully
        -- optimized.
        simplifier rewrittenPattern
    (mergedPatt, _) <-
        OrOfExpandedPattern.mergeWithPredicateSubstitution
            tools
            wrappedSimplifier
            PredicateSubstitution
                { predicate = rewritingCondition
                , substitution = rewrittenSubstitution
                }
            pattOr
    (evaluatedPatt, _) <-
        OrOfExpandedPattern.traverseWithPairs
            (evaluatePredicate tools wrappedSimplifier)
            mergedPatt
    return
        ( AttemptedFunction.Applied evaluatedPatt
        , ()
        )

evaluatePredicate
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PureMLPatternSimplifier level domain variable
    -- ^ Evaluates functions in a pattern.
    -> ExpandedPattern level domain variable
    -- ^ The condition to be evaluated.
    -> Simplifier (ExpandedPattern level domain variable, ())
evaluatePredicate
    tools
    simplifier
    ExpandedPattern {term, predicate, substitution}
  = do
    (   PredicateSubstitution
            { predicate = evaluatedPredicate
            , substitution = evaluatedSubstitution
            }
        , _
        ) <- give (sortTools tools) Predicate.evaluate simplifier predicate
    (   PredicateSubstitution
            { predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , _
        ) <- Except.lift
            (mergePredicatesAndSubstitutions
                tools
                [evaluatedPredicate]
                [substitution, evaluatedSubstitution]
            )
    -- TODO(virgil): Do I need to re-evaluate the predicate?
    return
        ( ExpandedPattern
            { term = term
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , ()
        )
