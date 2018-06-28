{-# LANGUAGE GADTs #-}
{-|
Module      : Data.Kore.Step.Condition.Evaluator
Description : Evaluates conditions
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Step.Condition.Evaluator
    ( evaluateFunctionCondition
    ) where

import           Data.Kore.AST.Common                 (And (..), Equals (..),
                                                       Iff (..), Implies (..),
                                                       Not (..), Or (..),
                                                       Pattern (..), Sort (..),
                                                       Variable)
import           Data.Kore.AST.PureML                 (CommonPurePattern,
                                                       asPurePattern,
                                                       fromPurePattern)
import           Data.Kore.Step.Condition.Condition   (EvaluatedCondition (..),
                                                       UnevaluatedCondition (..),
                                                       makeEvaluatedAnd,
                                                       makeEvaluatedIff,
                                                       makeEvaluatedImplies,
                                                       makeEvaluatedNot,
                                                       makeEvaluatedOr)
import           Data.Kore.Step.Function.Data         (CommonPurePatternFunctionEvaluator (..),
                                                       FunctionResult (..))
import           Data.Kore.Variables.Fresh.IntCounter (IntCounter)


evaluateFunctionCondition
    :: CommonPurePatternFunctionEvaluator level
    -> Sort level
    -> UnevaluatedCondition level
    -> IntCounter (EvaluatedCondition level)
evaluateFunctionCondition
    functionEvaluator
    conditionSort
    (UnevaluatedCondition condition)
  =
    evaluateFunctionConditionInternal
        functionEvaluator
        conditionSort
        (fromPurePattern condition)

evaluateFunctionConditionInternal
    :: CommonPurePatternFunctionEvaluator level
    -> Sort level
    -> Pattern level Variable (CommonPurePattern level)
    -> IntCounter (EvaluatedCondition level)
evaluateFunctionConditionInternal
    functionEvaluator
    conditionSort
    (AndPattern And {andFirst = first, andSecond = second})
  = do
    a <- evaluateFunctionConditionInternal functionEvaluator conditionSort (fromPurePattern first)
    b <- evaluateFunctionConditionInternal functionEvaluator conditionSort (fromPurePattern second)
    return $ makeEvaluatedAnd conditionSort a b
evaluateFunctionConditionInternal
    functionEvaluator
    conditionSort
    (OrPattern Or {orFirst = first, orSecond = second})
  = do
    a <- evaluateFunctionConditionInternal functionEvaluator conditionSort (fromPurePattern first)
    b <- evaluateFunctionConditionInternal functionEvaluator conditionSort (fromPurePattern second)
    return $ makeEvaluatedOr conditionSort a b
evaluateFunctionConditionInternal
    functionEvaluator
    conditionSort
    (NotPattern Not {notChild = patt})
  = do
    a <- evaluateFunctionConditionInternal functionEvaluator conditionSort (fromPurePattern patt)
    return (makeEvaluatedNot conditionSort a)
evaluateFunctionConditionInternal
    functionEvaluator
    conditionSort
    (ImpliesPattern Implies {impliesFirst = first, impliesSecond = second})
  = do
    a <- evaluateFunctionConditionInternal functionEvaluator conditionSort (fromPurePattern first)
    b <- evaluateFunctionConditionInternal functionEvaluator conditionSort (fromPurePattern second)
    return $ makeEvaluatedImplies conditionSort a b
evaluateFunctionConditionInternal
    functionEvaluator
    conditionSort
    (IffPattern Iff {iffFirst = first, iffSecond = second})
  = do
    a <- evaluateFunctionConditionInternal functionEvaluator conditionSort (fromPurePattern first)
    b <- evaluateFunctionConditionInternal functionEvaluator conditionSort (fromPurePattern second)
    return $ makeEvaluatedIff conditionSort a b
evaluateFunctionConditionInternal
    (CommonPurePatternFunctionEvaluator functionEvaluator)
    conditionSort
    (EqualsPattern Equals {equalsFirst = first, equalsSecond = second})
  = do
    firstValue <- functionEvaluator first
    secondValue <- functionEvaluator second
    let
        FunctionResult
            { functionResultPattern   = firstPattern
            , functionResultCondition = firstCondition
            } = firstValue
        FunctionResult
            { functionResultPattern   = secondPattern
            -- TODO: Maybe Make two types of condition: functionResult and evaluated
            , functionResultCondition = secondCondition
            } = secondValue
    -- TODO: This is more complex than implemented here, e.g. commutativity
    -- may be an issue.
    --firstCondition' <- firstCondition
    --secondCondition' <- secondCondition
    if firstPattern == secondPattern
        -- TODO: this should probably call evaluateFunctionCondition
        then return $ makeEvaluatedAnd conditionSort firstCondition secondCondition
        else return ConditionFalse
evaluateFunctionConditionInternal
    _ _ (TopPattern _)
  = return ConditionTrue
evaluateFunctionConditionInternal
    _ _ (BottomPattern _)
  = return ConditionFalse
evaluateFunctionConditionInternal
    _ _ patt
  = return (ConditionUnevaluable (asPurePattern patt))
