{-# LANGUAGE GADTs #-}
{-|
Module      : Data.Kore.Step.Function.UserDefined
Description : Evaluates user-defined functions in a pattern.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Step.Function.UserDefined
    ( CommonPurePatternFunctionEvaluator
    , axiomFunctionEvaluator
    ) where

import           Data.Kore.AST.Common                  (Application (..),
                                                        Pattern (..), Top (..))
import           Data.Kore.AST.MetaOrObject            (MetaOrObject)
import           Data.Kore.AST.PureML                  (CommonPurePattern,
                                                        asPurePattern)
import           Data.Kore.IndexedModule.MetadataTools (MetadataTools (..))
import           Data.Kore.Step.BaseStep               (AxiomPattern, StepperConfiguration (..),
                                                        stepWithAxiom)
import           Data.Kore.Step.Condition.Condition    (ConditionSort (..),
                                                        EvaluatedCondition (..),
                                                        UnevaluatedCondition (..),
                                                        makeEvaluatedAnd)
import           Data.Kore.Step.Function.Data          (AttemptedFunctionResult (..),
                                                        CommonPurePatternFunctionEvaluator (..),
                                                        ConditionEvaluator (..),
                                                        FunctionResult (..),
                                                        FunctionResultProof (..))
import           Data.Kore.Step.StepperAttributes
import           Data.Kore.Variables.Fresh.IntCounter  (IntCounter)

{--| 'axiomFunctionEvaluator' evaluates a user-defined function. After
evaluating the function, it tries to re-evaluate all functions on the result.

The function is assumed to be defined through an axiom.
--}
axiomFunctionEvaluator
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> ConditionSort level
    -- ^ Sort used for conditions. This function assumes that all conditions
    -- have this sort and will use it to create new conditions.
    -> AxiomPattern level
    -- ^ Axiom defining the current function.
    -> ConditionEvaluator level
    -- ^ Evaluates conditions
    -> CommonPurePatternFunctionEvaluator level
    -- ^ Evaluates functions in patterns
    -> Application level (CommonPurePattern level)
    -- ^ The function on which to evaluate the current function.
    -> IntCounter (AttemptedFunctionResult level, FunctionResultProof level)
axiomFunctionEvaluator
    metadataTools
    conditionSort
    axiom
    (ConditionEvaluator conditionEvaluator)
    functionEvaluator
    app
  =
    case stepResult of
        Left _ ->
            return (AttemptedFunctionResultNotApplicable, FunctionResultProof)
        Right configurationWithProof ->
            do
                (   StepperConfiguration
                        { stepperConfigurationPattern = rewrittenPattern
                        , stepperConfigurationCondition = rewritingCondition
                        }
                    , _
                    ) <- configurationWithProof
                -- TODO(virgil): Get the step substitution and use it on the
                -- condition.
                (evaluatedRewritingCondition, _) <-
                    conditionEvaluator (UnevaluatedCondition rewritingCondition)
                reevaluateFunctions
                    conditionSort
                    functionEvaluator
                    FunctionResult
                        { functionResultPattern   = rewrittenPattern
                        , functionResultCondition = evaluatedRewritingCondition
                        }
  where
    stepResult =
        stepWithAxiom
            metadataTools
            (stepperConfiguration conditionSort app)
            axiom
    stepperConfiguration
        :: ConditionSort level
        -> Application level (CommonPurePattern level)
        -> StepperConfiguration level
    stepperConfiguration conditionSort'@(ConditionSort sort) app' =
        StepperConfiguration
            { stepperConfigurationPattern =
                asPurePattern $ ApplicationPattern app'
            , stepperConfigurationCondition =
                asPurePattern $ TopPattern $ Top sort
            , stepperConfigurationConditionSort = conditionSort'
            }

{--| 'reevaluateFunctions' re-evaluates functions after a user-defined function
was evaluated.
--}
reevaluateFunctions
    :: ConditionSort level
    -- ^ Sort used for conditions. This function assumes that all conditions
    -- have this sort and will use it to create new conditions.
    -> CommonPurePatternFunctionEvaluator level
    -- ^ Evaluates functions in patterns.
    -> FunctionResult level
    -- ^ Function evaluation result.
    -> IntCounter (AttemptedFunctionResult level, FunctionResultProof level)
reevaluateFunctions
    conditionSort
    (CommonPurePatternFunctionEvaluator functionEvaluator)
    FunctionResult
        { functionResultPattern   = rewrittenPattern
        , functionResultCondition = rewritingCondition
        }
  = case rewritingCondition of
        ConditionFalse ->
            return (AttemptedFunctionResultNotApplicable, FunctionResultProof)
        _ -> do
            ( FunctionResult
                { functionResultPattern = simplifiedPattern
                , functionResultCondition = simplificationCondition
                }
             , _
             -- TODO(virgil): This call should be done in Evaluator.hs, but,
             -- for optimization purposes, it's done here. Make sure that
             -- this still makes sense after the evaluation code is fully
             -- optimized.
             ) <- functionEvaluator rewrittenPattern
            return
                ( firstSatisfiablePattern
                    [   ( simplifiedPattern
                        -- TODO(virgil): Maybe evaluate the 'and'
                        , fst $ makeEvaluatedAnd
                            conditionSort
                            rewritingCondition
                            simplificationCondition
                        )
                    -- TODO(virgil): Returning the rewrittenPattern here is
                    -- fishy.
                    , (rewrittenPattern, rewritingCondition)
                    ]
                , FunctionResultProof
                )

{--| Returns the first pattern if its condition might be satisfiable, otherwise
returns the second. Assumes that at least one pattern might be satisfiable.
--}
firstSatisfiablePattern
    :: [(CommonPurePattern level, EvaluatedCondition level)]
    -> AttemptedFunctionResult level
firstSatisfiablePattern
    ((patt, ConditionTrue) : _)
  = AttemptedFunctionResultApplied FunctionResult
        { functionResultPattern   = patt
        , functionResultCondition = ConditionTrue
        }
firstSatisfiablePattern
    ((patt, condition @ (ConditionUnevaluable _)) : _)
  = AttemptedFunctionResultApplied FunctionResult
        { functionResultPattern   = patt
        , functionResultCondition = condition
        }
firstSatisfiablePattern
    ((_, ConditionFalse) : reminder)
  = firstSatisfiablePattern reminder
firstSatisfiablePattern [] =
    error "Unexpected case."
