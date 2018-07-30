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
    ( PureMLPatternFunctionEvaluator
    , axiomFunctionEvaluator
    ) where

import Kore.AST.Common
       ( Application (..), Pattern (..), SortedVariable )
import Kore.AST.MetaOrObject
       ( MetaOrObject )
import Kore.AST.PureML
       ( CommonPurePattern, PureMLPattern, asPurePattern )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools (..) )
import Kore.Predicate.Predicate
       ( pattern PredicateFalse, makeTruePredicate )
import Kore.Step.BaseStep
       ( AxiomPattern, stepWithAxiom )
import Kore.Step.ExpandedPattern as ExpandedPattern
       ( ExpandedPattern (..), bottom )
import Kore.Step.Function.Data as AttemptedFunction
       ( AttemptedFunction (..) )
import Kore.Step.Function.Data
       ( CommonAttemptedFunction, CommonConditionEvaluator,
       CommonPurePatternFunctionEvaluator, ConditionEvaluator (..),
       FunctionResultProof (..), PureMLPatternFunctionEvaluator (..) )
import Kore.Step.StepperAttributes
       ( StepperAttributes )
import Kore.Step.Substitution
       ( mergePredicatesAndSubstitutions )
import Kore.Variables.Fresh.IntCounter
       ( IntCounter )

{-| 'axiomFunctionEvaluator' evaluates a user-defined function. After
evaluating the function, it tries to re-evaluate all functions on the result.

The function is assumed to be defined through an axiom.
-}
axiomFunctionEvaluator
    ::  ( MetaOrObject level)
    => AxiomPattern level
    -- ^ Axiom defining the current function.
    -> MetadataTools level StepperAttributes
    -> CommonConditionEvaluator level
    -- ^ Evaluates conditions
    -> CommonPurePatternFunctionEvaluator level
    -- ^ Evaluates functions in patterns
    -> Application level (CommonPurePattern level)
    -- ^ The function on which to evaluate the current function.
    -> IntCounter (CommonAttemptedFunction level, FunctionResultProof level)
axiomFunctionEvaluator
    axiom
    tools
    (ConditionEvaluator conditionEvaluator)
    functionEvaluator
    app
  =
    case stepResult of
        -- TODO: Make sure that Left excludes bottom results
        Left _ ->
            return (AttemptedFunction.NotApplicable, FunctionResultProof)
        Right configurationWithProof ->
            do
                (   ExpandedPattern
                        { term = rewrittenPattern
                        , predicate = rewritingCondition
                        , substitution = rewritingSubstitution
                        }
                    , _
                    ) <- configurationWithProof
                (evaluatedRewritingCondition, _) <-
                    conditionEvaluator rewritingCondition
                case evaluatedRewritingCondition of
                    PredicateFalse ->
                        return
                            ( AttemptedFunction.Applied ExpandedPattern.bottom
                            , FunctionResultProof
                            )
                    _ ->
                        reevaluateFunctions
                            tools
                            (ConditionEvaluator conditionEvaluator)
                            functionEvaluator
                            ExpandedPattern
                                { term   = rewrittenPattern
                                , predicate = evaluatedRewritingCondition
                                , substitution = rewritingSubstitution
                                }
  where
    stepResult =
        stepWithAxiom
            tools
            (stepperConfiguration app)
            axiom
    stepperConfiguration
        :: MetaOrObject level
        => Application level (PureMLPattern level variable)
        -> ExpandedPattern level variable
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
        , Show (variable level))
    => MetadataTools level StepperAttributes
    -> ConditionEvaluator level variable
    -- ^ Evaluates conditions
    -> PureMLPatternFunctionEvaluator level variable
    -- ^ Evaluates functions in patterns.
    -> ExpandedPattern level variable
    -- ^ Function evaluation result.
    -> IntCounter (AttemptedFunction level variable, FunctionResultProof level)
reevaluateFunctions
    tools
    (ConditionEvaluator conditionEvaluator)
    (PureMLPatternFunctionEvaluator functionEvaluator)
    ExpandedPattern
        { term   = rewrittenPattern
        , predicate = rewritingCondition
        , substitution = rewrittenSubstitution
        }
  = do
    ( ExpandedPattern
        { term = simplifiedPattern
        , predicate = simplificationCondition
        , substitution = simplificationSubstitution
        }
        , _  -- TODO: Use this proof
        -- TODO(virgil): This call should be done in Evaluator.hs, but,
        -- for optimization purposes, it's done here. Make sure that
        -- this still makes sense after the evaluation code is fully
        -- optimized.
        ) <- functionEvaluator rewrittenPattern
    let
        (mergedCondition, mergedSubstitution, _) =
            mergePredicatesAndSubstitutions
                tools
                [rewritingCondition, simplificationCondition]
                [rewrittenSubstitution, simplificationSubstitution]
    (evaluatedMergedCondition, _) <- conditionEvaluator mergedCondition
    case evaluatedMergedCondition of
        PredicateFalse -> return
            ( AttemptedFunction.Applied ExpandedPattern.bottom
            , FunctionResultProof
            )
        _ -> return
            ( AttemptedFunction.Applied ExpandedPattern
                { term   = simplifiedPattern
                , predicate = evaluatedMergedCondition
                , substitution = mergedSubstitution
                }
            , FunctionResultProof
            )
