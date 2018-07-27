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
import Kore.Step.OrOfExpandedPattern
       ( OrOfExpandedPattern )
import Kore.Step.Simplification.Data
       ( PureMLPatternSimplifier, SimplificationProof (..) )
import Kore.Step.StepperAttributes
       ( StepperAttributes )
import Kore.Variables.Fresh.IntCounter
       ( IntCounter )

{--| 'ApplicationFunctionEvaluator' evaluates functions on an 'Application'
pattern. This can be either a built-in evaluator or a user-defined one.
--}
newtype ApplicationFunctionEvaluator level variable =
    ApplicationFunctionEvaluator
        (forall . ( MetaOrObject level)
        => MetadataTools level StepperAttributes
        -- ^ Tools for finding additional information about patterns
        -- such as their sorts, whether they are constructors or hooked.
        -> PureMLPatternSimplifier level variable
        -- ^ Function for simplifying patterns.
        -> Application level (PureMLPattern level variable)
        -- ^ Pattern to be evaluated, in case it is a function application
        -> IntCounter
            ( AttemptedFunction level variable
            -- ^ The result of applying the function
            , SimplificationProof level
            -- ^ Proof certifying that the function was applied correctly
            -- (placeholder for now).
            )
        )

{--| 'CommonApplicationFunctionEvaluator' particularizes
'ApplicationFunctionEvaluator' to 'Variable', following the same pattern as
the other `Common*` types.
--}
type CommonApplicationFunctionEvaluator level =
    ApplicationFunctionEvaluator level Variable

{--| 'AttemptedFunction' is a generalized 'FunctionResult' that handles
cases where the function can't be fully evaluated.
--}
data AttemptedFunction level variable
    = NotApplicable
    | Applied !(OrOfExpandedPattern level variable)
  deriving (Show, Eq)

{--| 'CommonAttemptedFunction' particularizes 'AttemptedFunction' to 'Variable',
following the same pattern as the other `Common*` types.
--}
type CommonAttemptedFunction level = AttemptedFunction level Variable
