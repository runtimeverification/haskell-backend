module Test.Data.Kore.Step.Function (mockFunctionEvaluator) where

import           Test.Data.Kore.Comparators           ()

import           Data.Kore.AST.MetaOrObject           (MetaOrObject)
import           Data.Kore.AST.PureML                 (CommonPurePattern)
import           Data.Kore.Predicate.Predicate        (makeTruePredicate)
import           Data.Kore.Step.ExpandedPattern       as ExpandedPattern (ExpandedPattern (..))
import           Data.Kore.Step.ExpandedPattern       (CommonExpandedPattern)
import           Data.Kore.Step.Function.Data         (CommonPurePatternFunctionEvaluator,
                                                       FunctionResultProof (..),
                                                       PureMLPatternFunctionEvaluator (..))
import           Data.Kore.Variables.Fresh.IntCounter

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
