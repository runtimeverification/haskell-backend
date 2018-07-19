{-|
Module      : Data.Kore.Step.Function.Data
Description : Data structures used for function evaluation.
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
    , FunctionResultProof (..)
    , AttemptedFunctionResult (..)
    ) where

import Data.Kore.AST.Common
       ( Application )
import Data.Kore.AST.PureML
       ( CommonPurePattern )
import Data.Kore.Step.Condition.Condition
       ( ConditionProof, EvaluatedCondition, UnevaluatedCondition )
import Data.Kore.Variables.Fresh.IntCounter
       ( IntCounter )

{--| 'FunctionResultProof' is a placeholder for proofs showing that a Kore
function evaluation was correct.
--}
data FunctionResultProof level = FunctionResultProof
    deriving (Show, Eq)

{--| 'CommonPurePatternFunctionEvaluator' wraps a function that evaluates
Kore functions on patterns.
--}
newtype CommonPurePatternFunctionEvaluator level =
    CommonPurePatternFunctionEvaluator
        ( CommonPurePattern level
        -> IntCounter (FunctionResult level, FunctionResultProof level)
        )

{--| 'ApplicationFunctionEvaluator' evaluates functions on an 'Application'
pattern. This can be either a built-in evaluator or a user-defined one.
--}
newtype ApplicationFunctionEvaluator level =
    ApplicationFunctionEvaluator
        ( ConditionEvaluator level
        -> CommonPurePatternFunctionEvaluator level
        -> Application level (CommonPurePattern level)
        -> IntCounter (AttemptedFunctionResult level, FunctionResultProof level)
        )

{--| 'FunctionResult' represents the result of evaluating a Kore function on
a pattern.
--}
-- TODO(virgil): Consider replacing this by a StepperConfiguration
data FunctionResult level = FunctionResult
    { functionResultPattern   :: !(CommonPurePattern level)
    , functionResultCondition :: !(EvaluatedCondition level)
    }
  deriving (Show, Eq)

{--| 'AttemptedFunctionResult' is a generalized 'FunctionResult' that handles
cases where the function can't be fully evaluated.
--}
data AttemptedFunctionResult level
    = AttemptedFunctionResultNotApplicable
    | AttemptedFunctionResultSymbolic !(EvaluatedCondition level)
    | AttemptedFunctionResultApplied !(FunctionResult level)
  deriving (Show, Eq)

{--| 'ConditionEvaluator' is a wrapper for a function that evaluates conditions.
--}
newtype ConditionEvaluator level = ConditionEvaluator
    (  UnevaluatedCondition level
    -> IntCounter (EvaluatedCondition level, ConditionProof level)
    )
