{-|
Module      : Kore.Step.Function.Data
Description : Data structures used for function evaluation.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Function.Data
    ( ApplicationFunctionEvaluator (..)
    , CommonApplicationFunctionEvaluator
    , PureMLPatternFunctionEvaluator (..)
    , CommonPurePatternFunctionEvaluator
    , ConditionEvaluator (..)
    , CommonConditionEvaluator
    , FunctionResultProof (..)
    , AttemptedFunction (..)
    , CommonAttemptedFunction
    ) where

import Kore.AST.Common
       ( Application, Variable )
import Kore.AST.MetaOrObject
       ( MetaOrObject )
import Kore.AST.PureML
       ( PureMLPattern )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools )
import Kore.Predicate.Predicate
       ( Predicate, PredicateProof )
import Kore.Step.ExpandedPattern
       ( ExpandedPattern )
import Kore.Step.StepperAttributes
       ( StepperAttributes )
import Kore.Variables.Fresh.IntCounter
       ( IntCounter )

{--| 'FunctionResultProof' is a placeholder for proofs showing that a Kore
function evaluation was correct.
--}
data FunctionResultProof level = FunctionResultProof
    deriving (Show, Eq)

{--| 'PureMLPatternFunctionEvaluator' wraps a function that evaluates
Kore functions on PureMLPatterns.
--}
newtype PureMLPatternFunctionEvaluator level variable =
    PureMLPatternFunctionEvaluator
        ( PureMLPattern level variable
        -> IntCounter
            ( ExpandedPattern level variable
            , FunctionResultProof level
            )
        )
{--| 'CommonPurePatternFunctionEvaluator' wraps a function that evaluates
Kore functions on CommonPurePatterns.
--}
type CommonPurePatternFunctionEvaluator level =
    PureMLPatternFunctionEvaluator level Variable

{--| 'ApplicationFunctionEvaluator' evaluates functions on an 'Application'
pattern. This can be either a built-in evaluator or a user-defined one.
--}
newtype ApplicationFunctionEvaluator level variable =
    ApplicationFunctionEvaluator
        (forall . ( MetaOrObject level)
        => MetadataTools level StepperAttributes
        -> ConditionEvaluator level variable
        -> PureMLPatternFunctionEvaluator level variable
        -> Application level (PureMLPattern level variable)
        -> IntCounter
            ( AttemptedFunction level variable
            , FunctionResultProof level
            )
        )

type CommonApplicationFunctionEvaluator level =
    ApplicationFunctionEvaluator level Variable

{--| 'AttemptedFunction' is a generalized 'FunctionResult' that handles
cases where the function can't be fully evaluated.
--}
data AttemptedFunction level variable
    = NotApplicable
    | Applied !(ExpandedPattern level variable)
  deriving (Show, Eq)

{--| 'CommonAttemptedFunction' particularizes 'AttemptedFunction' to 'Variable',
following the same pattern as the other `Common*` types.
--}
type CommonAttemptedFunction level = AttemptedFunction level Variable

{--| 'ConditionEvaluator' is a wrapper for a function that evaluates conditions.
--}
newtype ConditionEvaluator level variable = ConditionEvaluator
    (  Predicate level variable
    -> IntCounter (Predicate level variable, PredicateProof level)
    )

type CommonConditionEvaluator level = ConditionEvaluator level Variable
