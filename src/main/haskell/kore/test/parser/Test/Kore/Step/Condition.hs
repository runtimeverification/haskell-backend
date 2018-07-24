module Test.Kore.Step.Condition (mockConditionEvaluator) where

import Kore.Step.Condition.Condition
       ( ConditionProof (..), EvaluatedCondition (..),
       UnevaluatedCondition (..) )
import Kore.Step.Function.Data
       ( ConditionEvaluator (..) )
import Kore.Variables.Fresh.IntCounter

mockConditionEvaluator
    ::  [   ( UnevaluatedCondition level
            , (EvaluatedCondition level, ConditionProof level)
            )
        ]
    -> ConditionEvaluator level
mockConditionEvaluator values =
    ConditionEvaluator (mockConditionEvaluatorHelper values)

mockConditionEvaluatorHelper
    ::  [   ( UnevaluatedCondition level
            , (EvaluatedCondition level, ConditionProof level)
            )
        ]
    -> UnevaluatedCondition level
    -> IntCounter (EvaluatedCondition level, ConditionProof level)
mockConditionEvaluatorHelper [] (UnevaluatedCondition condition) =
    return
        ( ConditionUnevaluable condition
        , ConditionProof
        )
mockConditionEvaluatorHelper
    ((condition, result) : reminder)
    unevaluatedCondition
  =
    if condition == unevaluatedCondition
        then return result
        else mockConditionEvaluatorHelper reminder unevaluatedCondition
