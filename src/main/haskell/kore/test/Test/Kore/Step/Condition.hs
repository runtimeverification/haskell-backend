module Test.Kore.Step.Condition (mockConditionEvaluator) where

import Kore.Predicate.Predicate
       ( Predicate, PredicateProof (..) )
import Kore.Step.Function.Data
       ( ConditionEvaluator (..) )
import Kore.Variables.Fresh.IntCounter

mockConditionEvaluator
    :: (Eq level, Eq (variable level))
    =>  [   ( Predicate level variable
            , (Predicate level variable, PredicateProof level)
            )
        ]
    -> ConditionEvaluator level variable
mockConditionEvaluator values =
    ConditionEvaluator (mockConditionEvaluatorHelper values)

mockConditionEvaluatorHelper
    :: (Eq level, Eq (variable level))
    =>  [   ( Predicate level variable
            , (Predicate level variable, PredicateProof level)
            )
        ]
    -> Predicate level variable
    -> IntCounter (Predicate level variable, PredicateProof level)
mockConditionEvaluatorHelper [] condition =
    return
        ( condition
        , PredicateProof
        )
mockConditionEvaluatorHelper
    ((condition, result) : reminder)
    unevaluatedCondition
  =
    if condition == unevaluatedCondition
        then return result
        else mockConditionEvaluatorHelper reminder unevaluatedCondition
