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

import           Kore.AST.MetaOrObject
                 ( MetaOrObject )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.Predicate.Predicate as Predicate
                 ( isFalse )
import           Kore.Step.BaseStep
                 ( AxiomPattern, StepProof (..), stepWithAxiom )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( CommonExpandedPattern, ExpandedPattern (..) )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Variables.Fresh.IntCounter
                 ( IntCounter, findState )

data MaxStepCount
    = MaxStepCount Integer
    | AnyStepCount

{-| 'step' executes a single rewriting step using the provided axioms.

Does not handle properly various cases, among which:
sigma(x, y) => y    vs    a
-}
step
    ::  ( MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> ExpandedPattern.CommonExpandedPattern level
    -- ^ Configuration being rewritten.
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    ->  [ IntCounter
            (ExpandedPattern.CommonExpandedPattern level, StepProof level)
        ]
step tools configuration axioms =
    rights $ map (stepWithAxiom tools configuration) axioms

{-| 'pickFirstStepper' rewrites a configuration using the provided axioms
until it cannot be rewritten anymore or until the step limit has been reached.
Whenever multiple axioms can be applied, it picks the first one whose
'Predicate' is not false and continues with that.

Does not handle properly various cases, among which:
sigma(x, y) => y    vs    a
-}
pickFirstStepper
    ::  ( MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> MaxStepCount
    -- ^ The maximum number of steps to be made
    -> ExpandedPattern.CommonExpandedPattern level
    -- ^ Configuration being rewritten.
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    -> IntCounter (ExpandedPattern.CommonExpandedPattern level, StepProof level)
pickFirstStepper _ (MaxStepCount 0) stepperConfiguration _ =
    return (stepperConfiguration, StepProofCombined [])
pickFirstStepper _ (MaxStepCount n) _ _ | n < 0 =
    error ("Negative MaxStepCount: " ++ show n)
pickFirstStepper
    tools (MaxStepCount maxStep) stepperConfiguration axioms
  =
    pickFirstStepperSkipMaxCheck
        tools (MaxStepCount (maxStep - 1)) stepperConfiguration axioms
pickFirstStepper tools AnyStepCount stepperConfiguration axioms =
    pickFirstStepperSkipMaxCheck
        tools AnyStepCount stepperConfiguration axioms

pickFirstStepperSkipMaxCheck
    ::  ( MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> MaxStepCount
    -- ^ The maximum number of steps to be made
    -> ExpandedPattern.CommonExpandedPattern level
    -- ^ Configuration being rewritten.
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    -> IntCounter (ExpandedPattern.CommonExpandedPattern level, StepProof level)
pickFirstStepperSkipMaxCheck
    tools maxStepCount stepperConfiguration axioms
  = do
    fnf <-
        findState
            (not . Predicate.isFalse . ExpandedPattern.predicate . fst)
            (step tools stepperConfiguration axioms)
    case fnf of
        Nothing -> return (stepperConfiguration, StepProofCombined [])
        Just (nextConfiguration, nextProof) ->
            do
            (finalConfiguration, finalProof) <-
                pickFirstStepper
                    tools maxStepCount nextConfiguration axioms
            return
                ( finalConfiguration
                , StepProofCombined [nextProof, finalProof]
                )
