{-|
Module      : Data.Kore.Step.Function.Data
Description : Data structures used for function evaluation
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Step.Function.Data
    ( ApplicationFunctionEvaluator (..)
    , CommonPurePatternFunctionEvaluator (..)
    , ConditionEvaluator (..)
    , FunctionResult (..)
    , FunctionEvaluation (..)
    ) where

import           Data.Kore.AST.Common                 (Application)
import           Data.Kore.AST.PureML                 (CommonPurePattern)
import           Data.Kore.Step.Condition.Condition   (EvaluatedCondition,
                                                       UnevaluatedCondition)
import           Data.Kore.Variables.Fresh.IntCounter (IntCounter)

newtype CommonPurePatternFunctionEvaluator level =
    CommonPurePatternFunctionEvaluator
        (CommonPurePattern level -> IntCounter (FunctionResult level))

newtype ApplicationFunctionEvaluator level =
    ApplicationFunctionEvaluator
        (  ConditionEvaluator level
        -> CommonPurePatternFunctionEvaluator level
        -> Application level (CommonPurePattern level)
        -> IntCounter (FunctionEvaluation level)
        )

-- TODO: this should probably be replaced by a StepperConfiguration
data FunctionResult level = FunctionResult
    { functionResultPattern   :: !(CommonPurePattern level)
    , functionResultCondition :: !(EvaluatedCondition level)
    }
  deriving (Show, Eq)

data FunctionEvaluation level
    = NotApplicable
    | Symbolic !(EvaluatedCondition level)
    | Applied !(FunctionResult level)
  deriving (Show, Eq)

newtype ConditionEvaluator level = ConditionEvaluator
    (UnevaluatedCondition level -> IntCounter (EvaluatedCondition level))
