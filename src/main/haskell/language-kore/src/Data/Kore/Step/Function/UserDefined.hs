{-# LANGUAGE GADTs #-}
{-|
Module      : Data.Kore.Step.Function.UserDefined
Description : Evaluates user-defined functions in a pattern
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
                                                        Pattern (..), Sort (..),
                                                        Top (..))
import           Data.Kore.AST.MetaOrObject            (MetaOrObject)
import           Data.Kore.AST.PureML                  (CommonPurePattern,
                                                        asPurePattern)
import           Data.Kore.IndexedModule.MetadataTools (MetadataTools (..))
import           Data.Kore.Step.BaseStep               (AxiomPattern, StepperConfiguration (..),
                                                        stepWithAxiom)
import           Data.Kore.Step.Condition.Condition    (EvaluatedCondition (..), UnevaluatedCondition (..),
                                                        makeEvaluatedAnd)
import           Data.Kore.Step.Function.Data          (CommonPurePatternFunctionEvaluator (..),
                                                        ConditionEvaluator (..),
                                                        FunctionEvaluation (..),
                                                        FunctionResult (..))
import           Data.Kore.Variables.Fresh.IntCounter  (IntCounter)

axiomFunctionEvaluator
    :: MetaOrObject level
    => MetadataTools level
    -> Sort level
    -> AxiomPattern level
    -> ConditionEvaluator level
    -> CommonPurePatternFunctionEvaluator level
    -> Application level (CommonPurePattern level)
    -> IntCounter (FunctionEvaluation level)
axiomFunctionEvaluator
    metadataTools
    conditionSort
    axiom
    (ConditionEvaluator conditionEvaluator)
    functionEvaluator
    app
  = --trace "axiomFunctionEvaluator" $
    case stepResult of
        Left _ -> {-do
            e <- err
            trace ("axiomFunctionEvaluator-Left " ++ show e) $ -}return NotApplicable
        Right configurationWithProof -> --trace "axiomFunctionEvaluator-Right" $
            do
                (   StepperConfiguration
                        { stepperConfigurationPattern = rewrittenPattern
                        , stepperConfigurationCondition = rewritingCondition
                        }
                    , _
                    ) <- configurationWithProof
                evaluatedRewritingCondition <-
                    conditionEvaluator (UnevaluatedCondition rewritingCondition)
                --trace "" $ trace "---------------------------------" $ trace ("Pattern: " ++ unparseToString (patternPureToKore $ asPurePattern $ ApplicationPattern app) ++ "  -->  " ++ unparseToString (patternPureToKore rewrittenPattern)) $ trace ("Condition: " ++ prettyPrintToString evaluatedRewritingCondition) $ trace "---------------------------------" $
                axiomFunctionEvaluatorAfterStep
                        metadataTools
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
        :: Sort level
        -> Application level (CommonPurePattern level)
        -> StepperConfiguration level
    stepperConfiguration conditionSort' app' = StepperConfiguration
        { stepperConfigurationPattern = asPurePattern $ ApplicationPattern app'
        , stepperConfigurationCondition =
            asPurePattern $ TopPattern $ Top conditionSort'
        , stepperConfigurationConditionSort = conditionSort'
        }

axiomFunctionEvaluatorAfterStep
    :: MetadataTools level
    -> Sort level
    -> CommonPurePatternFunctionEvaluator level
    -> FunctionResult level
    -> IntCounter (FunctionEvaluation level)
axiomFunctionEvaluatorAfterStep
    _
    conditionSort
    (CommonPurePatternFunctionEvaluator functionEvaluator)
    FunctionResult
        { functionResultPattern   = rewrittenPattern
        , functionResultCondition = rewritingCondition
        }
  = case rewritingCondition of
        ConditionFalse -> return NotApplicable
        _ -> do
            FunctionResult
                { functionResultPattern = simplifiedPattern
                , functionResultCondition = simplificationCondition
                } <- functionEvaluator rewrittenPattern
            return $ resultFromSimplification
                conditionSort
                simplifiedPattern
                --TODO: Maybe call a ConditionEvaluator
                (makeEvaluatedAnd conditionSort rewritingCondition simplificationCondition)
                rewrittenPattern
                rewritingCondition

resultFromSimplification
    :: Sort level
    -> CommonPurePattern level
    -> EvaluatedCondition level
    -> CommonPurePattern level
    -> EvaluatedCondition level
    -> FunctionEvaluation level
resultFromSimplification
    _ simplifiedPattern ConditionTrue _ _
  = Applied FunctionResult
        { functionResultPattern   = simplifiedPattern
        , functionResultCondition = ConditionTrue
        }
resultFromSimplification
    _
    simplifiedPattern
    simplificationCondition @ (ConditionUnevaluable _)
    _ _
  = Applied FunctionResult
        { functionResultPattern   = simplifiedPattern
        , functionResultCondition = simplificationCondition
        }
resultFromSimplification
    _ _
    ConditionFalse
    rewrittenPattern
    ConditionTrue
  = Applied FunctionResult
        { functionResultPattern   = rewrittenPattern
        , functionResultCondition = ConditionTrue
        }
resultFromSimplification
    _ _
    ConditionFalse
    rewrittenPattern
    rewritingCondition @ (ConditionUnevaluable _)
  = Applied FunctionResult
        { functionResultPattern   = rewrittenPattern
        , functionResultCondition = rewritingCondition
        }
resultFromSimplification
    _ _ ConditionFalse _ ConditionFalse
  = error "Unexpected case."
