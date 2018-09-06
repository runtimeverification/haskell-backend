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

import qualified Control.Monad.Trans as Monad.Trans
import           Data.Either
                 ( rights )
import qualified Data.Map as Map

import           Kore.AST.Common
                 ( Id )
import           Kore.AST.MetaOrObject
                 ( MetaOrObject )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.BaseStep
                 ( AxiomPattern, StepProof (..), simplifyStepProof,
                 stepWithAxiom )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern )
import           Kore.Step.Function.Data
                 ( CommonApplicationFunctionEvaluator )
import           Kore.Step.OrOfExpandedPattern
                 ( CommonOrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, make, traverseFlattenWithPairs )
import           Kore.Step.Simplification.Data
                 ( Simplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
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
    ::  ( MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> Map.Map (Id level) [CommonApplicationFunctionEvaluator level domain]
    -- ^ Map from symbol IDs to defined functions
    -> [AxiomPattern level domain]
    -- ^ Rewriting axioms
    -> CommonOrOfExpandedPattern level domain
    -- ^ Configuration being rewritten.
    -> Simplifier
        (CommonOrOfExpandedPattern level domain, StepProof level)
step tools symbolIdToEvaluator axioms configuration = do
    (stepPattern, stepProofs) <- Monad.Trans.lift
        (OrOfExpandedPattern.traverseFlattenWithPairs
            (baseStepWithPattern tools axioms)
            configuration
        )
    (simplifiedPattern, simplificationProofs) <-
        OrOfExpandedPattern.traverseFlattenWithPairs
            (ExpandedPattern.simplify tools symbolIdToEvaluator)
            stepPattern
    return
        ( simplifiedPattern
        , simplifyStepProof $ StepProofCombined
            (map StepProofSimplification simplificationProofs ++ stepProofs)
        )

baseStepWithPattern
    ::  ( MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> [AxiomPattern level domain]
    -- ^ Rewriting axioms
    -> CommonExpandedPattern level domain
    -- ^ Configuration being rewritten.
    -> IntCounter (CommonOrOfExpandedPattern level domain, StepProof level)
baseStepWithPattern tools axioms configuration = do
    stepResultsWithProofs <- sequence (stepToList tools configuration axioms)
    let (results, proofs) = unzip stepResultsWithProofs
    return
        ( OrOfExpandedPattern.make results
        , simplifyStepProof $ StepProofCombined proofs
        )

stepToList
    ::  ( MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> CommonExpandedPattern level domain
    -- ^ Configuration being rewritten.
    -> [AxiomPattern level domain]
    -- ^ Rewriting axioms
    ->  [ IntCounter
            (CommonExpandedPattern level domain, StepProof level)
        ]
stepToList tools configuration axioms =
    -- TODO: Stop ignoring Left results. Also, how would a result
    -- to which I can't apply an axiom look like?
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
    -> Map.Map (Id level) [CommonApplicationFunctionEvaluator level domain]
    -- ^ Map from symbol IDs to defined functions
    -> [AxiomPattern level domain]
    -- ^ Rewriting axioms
    -> MaxStepCount
    -- ^ The maximum number of steps to be made
    -> CommonExpandedPattern level domain
    -- ^ Configuration being rewritten.
    -> Simplifier (CommonExpandedPattern level domain, StepProof level)
pickFirstStepper _ _ _ (MaxStepCount 0) stepperConfiguration =
    return (stepperConfiguration, StepProofCombined [])
pickFirstStepper _ _ _ (MaxStepCount n) _ | n < 0 =
    error ("Negative MaxStepCount: " ++ show n)
pickFirstStepper
    tools symbolIdToEvaluator axioms (MaxStepCount maxStep) stepperConfiguration
  =
    pickFirstStepperSkipMaxCheck
        tools
        symbolIdToEvaluator
        axioms
        (MaxStepCount (maxStep - 1))
        stepperConfiguration
pickFirstStepper
    tools symbolIdToEvaluator axioms AnyStepCount stepperConfiguration
  =
    pickFirstStepperSkipMaxCheck
        tools
        symbolIdToEvaluator
        axioms
        AnyStepCount
        stepperConfiguration

pickFirstStepperSkipMaxCheck
    ::  ( MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> Map.Map (Id level) [CommonApplicationFunctionEvaluator level domain]
    -- ^ Map from symbol IDs to defined functions
    -> [AxiomPattern level domain]
    -- ^ Rewriting axioms
    -> MaxStepCount
    -- ^ The maximum number of steps to be made
    -> CommonExpandedPattern level domain
    -- ^ Configuration being rewritten.
    -> Simplifier (CommonExpandedPattern level domain, StepProof level)
pickFirstStepperSkipMaxCheck
    tools symbolIdToEvaluator axioms maxStepCount stepperConfiguration
  = do
    (patterns, nextProof) <-
        -- TODO: Perhaps use IntCounter.findState to reduce the need for
        -- intCounter values and to make this more testable.
        step
            tools
            symbolIdToEvaluator
            axioms
            (OrOfExpandedPattern.make [stepperConfiguration])
    case OrOfExpandedPattern.extractPatterns patterns of
        [] -> return (stepperConfiguration, StepProofCombined [])
        (nextConfiguration : _) -> do
            (finalConfiguration, finalProof) <-
                pickFirstStepper
                    tools
                    symbolIdToEvaluator
                    axioms
                    maxStepCount
                    nextConfiguration
            return
                ( finalConfiguration
                , simplifyStepProof
                    $ StepProofCombined [nextProof, finalProof]
                )
