module Test.Kore.Step.Function (mockFunctionEvaluator) where

import Kore.AST.PureML
       ( CommonPurePattern )
import Kore.Step.Condition.Condition
import Kore.Step.Function.Data
       ( CommonPurePatternFunctionEvaluator (..), FunctionResult (..),
       FunctionResultProof (..) )
import Kore.Variables.Fresh.IntCounter

import Test.Kore.Comparators ()

mockFunctionEvaluator
    ::  [   ( CommonPurePattern level
            , (FunctionResult level, FunctionResultProof level)
            )
        ]
    -> CommonPurePatternFunctionEvaluator level
mockFunctionEvaluator values =
    CommonPurePatternFunctionEvaluator
        (mockFunctionEvaluatorHelper values)

mockFunctionEvaluatorHelper
    ::  [   ( CommonPurePattern level
            , (FunctionResult level, FunctionResultProof level)
            )
        ]
    -> CommonPurePattern level
    -> IntCounter (FunctionResult level, FunctionResultProof level)
mockFunctionEvaluatorHelper [] patt =
    return
        ( FunctionResult
            { functionResultPattern   = patt
            , functionResultCondition = ConditionTrue
            }
        , FunctionResultProof
        )
mockFunctionEvaluatorHelper
    ((left, result) : reminder)
    patt
  =
    if patt == left
        then return result
        else mockFunctionEvaluatorHelper reminder patt
