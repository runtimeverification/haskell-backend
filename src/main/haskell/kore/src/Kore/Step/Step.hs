{-|
Module      : Kore.Step.Step
Description : Single and multiple step execution
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Step
    ( step
    , pickFirstStepper
    , MaxStepCount(..)
    ) where

import           Data.Either
                 ( rights )
import qualified Data.Map as Map
import           Data.Semigroup
                 ( (<>) )

import           Kore.AST.Common
                 ( Id )
import           Kore.AST.MetaOrObject
                 ( MetaOrObject )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.BaseStep
                 ( AxiomPattern, StepProof (..), StepProofAtom (..), stepProof,
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
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Variables.Fresh

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
    -> Map.Map (Id level) [CommonApplicationFunctionEvaluator level]
    -- ^ Map from symbol IDs to defined functions
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    -> CommonOrOfExpandedPattern level
    -- ^ Configuration being rewritten.
    -> Simplifier
        (CommonOrOfExpandedPattern level, StepProof level)
step tools symbolIdToEvaluator axioms configuration = do
    (stepPattern, stepProofs) <-
        OrOfExpandedPattern.traverseFlattenWithPairs
            (baseStepWithPattern tools axioms)
            configuration
    (simplifiedPattern, simplificationProofs) <-
        OrOfExpandedPattern.traverseFlattenWithPairs
            (ExpandedPattern.simplify
                tools
                (Simplifier.create tools symbolIdToEvaluator)
            )
            stepPattern
    return
        ( simplifiedPattern
        , mconcat (stepProof . StepProofSimplification <$> simplificationProofs)
            <> mconcat stepProofs
        )

baseStepWithPattern
    ::  ( MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    -> CommonExpandedPattern level
    -- ^ Configuration being rewritten.
    -> Counter (CommonOrOfExpandedPattern level, StepProof level)
baseStepWithPattern tools axioms configuration = do
    stepResultsWithProofs <- sequence (stepToList tools configuration axioms)
    let (results, proofs) = unzip stepResultsWithProofs
    return
        ( OrOfExpandedPattern.make results
        , mconcat proofs
        )

stepToList
    ::  ( MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> CommonExpandedPattern level
    -- ^ Configuration being rewritten.
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    ->  [ Counter
            (CommonExpandedPattern level, StepProof level)
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
    -> Map.Map (Id level) [CommonApplicationFunctionEvaluator level]
    -- ^ Map from symbol IDs to defined functions
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    -> MaxStepCount
    -- ^ The maximum number of steps to be made
    -> CommonExpandedPattern level
    -- ^ Configuration being rewritten.
    -> Simplifier (CommonExpandedPattern level, StepProof level)
pickFirstStepper _ _ _ (MaxStepCount 0) stepperConfiguration =
    return (stepperConfiguration, mempty)
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
    -> Map.Map (Id level) [CommonApplicationFunctionEvaluator level]
    -- ^ Map from symbol IDs to defined functions
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    -> MaxStepCount
    -- ^ The maximum number of steps to be made
    -> CommonExpandedPattern level
    -- ^ Configuration being rewritten.
    -> Simplifier (CommonExpandedPattern level, StepProof level)
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
        [] -> return (stepperConfiguration, mempty)
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
                , nextProof <> finalProof
                )
