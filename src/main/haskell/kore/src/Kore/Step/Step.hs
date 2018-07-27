{-|
Module      : Kore.Step.Step
Description : Single and multiple step execution
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Step
    ( step
    , pickFirstStepper
    , MaxStepCount(..)
    ) where

import Data.Either
       ( rights )
import Data.Reflection
       ( Given )

import           Kore.AST.MetaOrObject
                 ( MetaOrObject )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.BaseStep
                 ( AxiomPattern, StepProof (..), stepWithAxiom )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Variables.Fresh.IntCounter
                 ( IntCounter )

data MaxStepCount
    = MaxStepCount Integer
    | AnyStepCount

{-| 'step' executes a single rewriting step using the provided axioms.

Does not handle properly various cases, among which:
sigma(x, y) => y    vs    a
-}
step
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        )
    => ExpandedPattern.CommonExpandedPattern level
    -- ^ Configuration being rewritten.
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    ->  [ IntCounter
            (ExpandedPattern.CommonExpandedPattern level, StepProof level)
        ]
step configuration axioms =
    rights $ map (stepWithAxiom configuration) axioms

{-| 'pickFirstStepper' rewrites a configuration using the provided axioms
until it cannot be rewritten anymore or until the step limit has been reached.
Whenever multiple axioms can be applied, it picks the first one and continues
with that.

Does not handle properly various cases, among which:
sigma(x, y) => y    vs    a
-}
pickFirstStepper
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        )
    => MaxStepCount
    -- ^ The maximum number of steps to be made
    -> ExpandedPattern.CommonExpandedPattern level
    -- ^ Configuration being rewritten.
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    -> IntCounter (ExpandedPattern.CommonExpandedPattern level, StepProof level)
pickFirstStepper (MaxStepCount 0) stepperConfiguration _ =
    return (stepperConfiguration, StepProofCombined [])
pickFirstStepper (MaxStepCount n) _ _ | n < 0 =
    error ("Negative MaxStepCount: " ++ show n)
pickFirstStepper
    (MaxStepCount maxStep) stepperConfiguration axioms
  =
    pickFirstStepperSkipMaxCheck
        (MaxStepCount (maxStep - 1)) stepperConfiguration axioms
pickFirstStepper AnyStepCount stepperConfiguration axioms =
    pickFirstStepperSkipMaxCheck
        AnyStepCount stepperConfiguration axioms

pickFirstStepperSkipMaxCheck
    ::  ( MetaOrObject level
        , Given (MetadataTools level)
        )
    => MaxStepCount
    -- ^ The maximum number of steps to be made
    -> ExpandedPattern.CommonExpandedPattern level
    -- ^ Configuration being rewritten.
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    -> IntCounter (ExpandedPattern.CommonExpandedPattern level, StepProof level)
pickFirstStepperSkipMaxCheck
    maxStepCount stepperConfiguration axioms
  =
    case step stepperConfiguration axioms of
        [] -> return (stepperConfiguration, StepProofCombined [])
        first : _ -> do
            (nextConfiguration, nextProof) <- first
            (finalConfiguration, finalProof) <-
                pickFirstStepper
                    maxStepCount nextConfiguration axioms
            return
                (finalConfiguration, StepProofCombined [nextProof, finalProof])
