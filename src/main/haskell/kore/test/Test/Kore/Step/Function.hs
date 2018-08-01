module Test.Kore.Step.Function (mockFunctionEvaluator) where

import Kore.AST.MetaOrObject
       ( MetaOrObject )
import Kore.AST.PureML
       ( CommonPurePattern )
import Kore.Predicate.Predicate
       ( makeTruePredicate )
import Kore.Step.ExpandedPattern as ExpandedPattern
       ( ExpandedPattern (..) )
import Kore.Step.ExpandedPattern
       ( CommonExpandedPattern )
import Kore.Step.Function.Data
       ( CommonPurePatternFunctionEvaluator, FunctionResultProof (..),
       PureMLPatternFunctionEvaluator (..) )
import Kore.Variables.Fresh.IntCounter

import Test.Kore.Comparators ()

mockFunctionEvaluator
    :: MetaOrObject level
    =>  [   ( CommonPurePattern level
            , (CommonExpandedPattern level, FunctionResultProof level)
            )
        ]
    -> CommonPurePatternFunctionEvaluator level
mockFunctionEvaluator values =
    PureMLPatternFunctionEvaluator
        (mockFunctionEvaluatorHelper values)

mockFunctionEvaluatorHelper
    :: MetaOrObject level
    =>  [   ( CommonPurePattern level
            , (CommonExpandedPattern level, FunctionResultProof level)
            )
        ]
    -> CommonPurePattern level
    -> IntCounter (CommonExpandedPattern level, FunctionResultProof level)
mockFunctionEvaluatorHelper [] patt =
    return
        ( ExpandedPattern
            { term   = patt
            , predicate = makeTruePredicate
            , substitution = []
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
