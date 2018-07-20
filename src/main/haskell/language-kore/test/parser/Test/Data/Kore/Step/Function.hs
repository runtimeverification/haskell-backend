module Test.Data.Kore.Step.Function (mockFunctionEvaluator) where

import           Test.Data.Kore.Comparators           ()

import           Data.Kore.AST.PureML                 (CommonPurePattern)
import           Data.Kore.Step.Condition.Condition
import           Data.Kore.Step.Function.Data         (CommonPurePatternFunctionEvaluator (..),
                                                       FunctionResult (..),
                                                       FunctionResultProof (..))
import           Data.Kore.Variables.Fresh.IntCounter

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
