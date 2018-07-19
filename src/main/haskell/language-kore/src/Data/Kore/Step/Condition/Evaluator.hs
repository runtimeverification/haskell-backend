{-# LANGUAGE GADTs #-}
{-|
Module      : Data.Kore.Step.Condition.Evaluator
Description : Evaluates conditions.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Step.Condition.Evaluator
    ( evaluateFunctionCondition
    ) where

import Data.Kore.AST.Common
       ( And (..), Equals (..), Iff (..), Implies (..), Not (..), Or (..),
       Pattern (..), Variable )
import Data.Kore.AST.PureML
       ( CommonPurePattern, asPurePattern, fromPurePattern )
import Data.Kore.Step.Condition.Condition
       ( ConditionProof (..), ConditionSort (..), EvaluatedCondition (..),
       UnevaluatedCondition (..), makeEvaluatedAnd, makeEvaluatedIff,
       makeEvaluatedImplies, makeEvaluatedNot, makeEvaluatedOr )
import Data.Kore.Step.Function.Data
       ( CommonPurePatternFunctionEvaluator (..), FunctionResult (..) )
import Data.Kore.Variables.Fresh.IntCounter
       ( IntCounter )

{--| 'evaluateFunctionCondition' attempts to evaluate a Kore condition.

Right now the evaluation is rather rudimentary and gives up failry easy,
returning 'ConditionUnevaluable'.
--}
evaluateFunctionCondition
    :: CommonPurePatternFunctionEvaluator level
    -- ^ Evaluates functions in a pattern.
    -> ConditionSort level
    -- ^ Sort used for conditions. This function assumes that all conditions
    -- have this sort and will use it to create new conditions.
    -> UnevaluatedCondition level
    -- ^ The condition to be evaluated.
    -> IntCounter (EvaluatedCondition level, ConditionProof level)
evaluateFunctionCondition
    functionEvaluator
    conditionSort
    (UnevaluatedCondition condition)
  =
    evaluateFunctionConditionInternal
        functionEvaluator
        conditionSort
        (fromPurePattern condition)

{--| 'evaluateFunctionCondition' attempts to evaluate a Kore condition.

Right now the evaluation is rather rudimentary and gives up failry easy,
returning 'ConditionUnevaluable'.
--}
evaluateFunctionConditionInternal
    :: CommonPurePatternFunctionEvaluator level
    -> ConditionSort level
    -> Pattern level Variable (CommonPurePattern level)
    -> IntCounter (EvaluatedCondition level, ConditionProof level)
evaluateFunctionConditionInternal
    functionEvaluator
    conditionSort
    (AndPattern And {andFirst = first, andSecond = second})
  = do
    (a, _) <- evaluateFunctionConditionInternal
        functionEvaluator conditionSort (fromPurePattern first)
    (b, _) <- evaluateFunctionConditionInternal
        functionEvaluator conditionSort (fromPurePattern second)
    return $ makeEvaluatedAnd conditionSort a b
evaluateFunctionConditionInternal
    functionEvaluator
    conditionSort
    (OrPattern Or {orFirst = first, orSecond = second})
  = do
    (a, _) <- evaluateFunctionConditionInternal
        functionEvaluator conditionSort (fromPurePattern first)
    (b, _) <- evaluateFunctionConditionInternal
        functionEvaluator conditionSort (fromPurePattern second)
    return $ makeEvaluatedOr conditionSort a b
evaluateFunctionConditionInternal
    functionEvaluator
    conditionSort
    (NotPattern Not {notChild = patt})
  = do
    (a, _) <- evaluateFunctionConditionInternal
        functionEvaluator conditionSort (fromPurePattern patt)
    return (makeEvaluatedNot conditionSort a)
evaluateFunctionConditionInternal
    functionEvaluator
    conditionSort
    (ImpliesPattern Implies {impliesFirst = first, impliesSecond = second})
  = do
    (a, _) <- evaluateFunctionConditionInternal
        functionEvaluator conditionSort (fromPurePattern first)
    (b, _) <- evaluateFunctionConditionInternal
        functionEvaluator conditionSort (fromPurePattern second)
    return $ makeEvaluatedImplies conditionSort a b
evaluateFunctionConditionInternal
    functionEvaluator
    conditionSort
    (IffPattern Iff {iffFirst = first, iffSecond = second})
  = do
    (a, _) <- evaluateFunctionConditionInternal
        functionEvaluator conditionSort (fromPurePattern first)
    (b, _) <- evaluateFunctionConditionInternal
        functionEvaluator conditionSort (fromPurePattern second)
    return $ makeEvaluatedIff conditionSort a b
evaluateFunctionConditionInternal
    (CommonPurePatternFunctionEvaluator functionEvaluator)
    conditionSort
    (EqualsPattern Equals {equalsFirst = first, equalsSecond = second})
  = do
    firstValue <- functionEvaluator first
    secondValue <- functionEvaluator second
    let
        (   FunctionResult
                { functionResultPattern   = firstPattern
                , functionResultCondition = firstCondition
                }
            , _
            ) = firstValue
        (   FunctionResult
                { functionResultPattern   = secondPattern
                , functionResultCondition = secondCondition
                }
            , _
            ) = secondValue
    -- TODO(virgil): This is wrong, because `variable=pattern` is not
    -- necessarily false. Fix this.
    if firstPattern == secondPattern
        -- TODO(virgil): this should probably call evaluateFunctionCondition
        then return $
            makeEvaluatedAnd conditionSort firstCondition secondCondition
        else return (ConditionFalse, ConditionProof)
evaluateFunctionConditionInternal
    _ _ (TopPattern _)
  = return (ConditionTrue, ConditionProof)
evaluateFunctionConditionInternal
    _ _ (BottomPattern _)
  = return (ConditionFalse, ConditionProof)
evaluateFunctionConditionInternal
    _ _ patt
  = return (ConditionUnevaluable (asPurePattern patt), ConditionProof)
