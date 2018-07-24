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

import Kore.AST.MetaOrObject
       ( MetaOrObject )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools )
import Kore.Step.BaseStep
       ( AxiomPattern, StepProof (..), StepperConfiguration, stepWithAxiom )
import Kore.Variables.Fresh.IntCounter
       ( IntCounter )

data MaxStepCount
    = MaxStepCount Integer
    | AnyStepCount

{--| 'step' executes a single rewriting step using the provided axioms.

Does not handle properly various cases, among which:
sigma(x, y) => y    vs    a
--}
step
    :: MetaOrObject level
    => MetadataTools level
    -- ^ Functions yielding metadata for pattern heads.
    -> StepperConfiguration level
    -- ^ Configuration being rewritten.
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    -> [IntCounter (StepperConfiguration level, StepProof level)]
step metadataTools configuration axioms =
    rights $ map (stepWithAxiom metadataTools configuration) axioms

{--| 'pickFirstStepper' rewrites a configuration using the provided axioms
until it cannot be rewritten anymore or until the step limit has been reached.
Whenever multiple axioms can be applied, it picks the first one and continues
with that.

Does not handle properly various cases, among which:
sigma(x, y) => y    vs    a
--}
pickFirstStepper
    :: MetaOrObject level
    => MetadataTools level
    -- ^ Functions yielding metadata for pattern heads.
    -> MaxStepCount
    -- ^ The maximum number of steps to be made
    -> StepperConfiguration level
    -- ^ Configuration being rewritten.
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    -> IntCounter (StepperConfiguration level, StepProof level)
pickFirstStepper _ (MaxStepCount 0) stepperConfiguration _ =
    return (stepperConfiguration, StepProofCombined [])
pickFirstStepper _ (MaxStepCount n) _ _ | n < 0 =
    error ("Negative MaxStepCount: " ++ show n)
pickFirstStepper
    metadataTools (MaxStepCount maxStep) stepperConfiguration axioms
  =
    pickFirstStepperSkipMaxCheck
        metadataTools (MaxStepCount (maxStep - 1)) stepperConfiguration axioms
pickFirstStepper metadataTools AnyStepCount stepperConfiguration axioms =
    pickFirstStepperSkipMaxCheck
        metadataTools AnyStepCount stepperConfiguration axioms

pickFirstStepperSkipMaxCheck
    :: MetaOrObject level
    => MetadataTools level
    -- ^ Functions yielding metadata for pattern heads.
    -> MaxStepCount
    -- ^ The maximum number of steps to be made
    -> StepperConfiguration level
    -- ^ Configuration being rewritten.
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    -> IntCounter (StepperConfiguration level, StepProof level)
pickFirstStepperSkipMaxCheck
    metadataTools maxStepCount stepperConfiguration axioms
  =
    case step metadataTools stepperConfiguration axioms of
        [] -> return (stepperConfiguration, StepProofCombined [])
        first : _ -> do
            (nextConfiguration, nextProof) <- first
            (finalConfiguration, finalProof) <-
                pickFirstStepper
                    metadataTools maxStepCount nextConfiguration axioms
            return
                (finalConfiguration, StepProofCombined [nextProof, finalProof])
