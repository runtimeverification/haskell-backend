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
    ( simpleStrategy
    , simpleStepper
    , stepStrategy
    , stepStepper
    , simpleRule
      -- * Primitive strategies
    , Prim (..)
    , axiom
    , builtin
      -- * Re-exports
    , Limit (..)
    , Natural
    ) where

import           Data.Foldable
                 ( toList )
import           Data.Semigroup
                 ( (<>) )

import           Kore.AST.MetaOrObject
                 ( MetaOrObject )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.BaseStep
                 (AxiomPattern, StepProof (..), simplificationProof, stepWithAxiom )

import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.OrOfExpandedPattern as ExpandedPattern
import           Kore.Step.Simplification.Data
                 ( CommonPureMLPatternSimplifier, Simplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Strategy
                 ( Limit (..), Strategy, runStrategy )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Variables.Fresh

stepStrategy
    :: MetaOrObject level
    => [AxiomPattern level]
    -> Strategy (Prim (AxiomPattern level))
stepStrategy axioms =
    Strategy.all (applyAxiom <$> axioms)
  where
    applyAxiom a = axiomStep a Strategy.stuck

axiomStep :: axiom -> Strategy (Prim axiom) -> Strategy (Prim axiom)
axiomStep a =
    Strategy.step . Strategy.apply (axiom a) . Strategy.apply builtin

stepStepper
    :: (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> CommonPureMLPatternSimplifier level
    -- ^ Map from symbol IDs to defined functions
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    -> (CommonExpandedPattern level, StepProof level)
    -- ^ Configuration being rewritten and its accompanying proof
    -> Simplifier [(CommonExpandedPattern level, StepProof level)]
stepStepper tools simplifier axioms =
    (<$>) Strategy.pickStuck . runStrategy rule strategy Unlimited
  where
    rule = simpleRule tools simplifier
    strategy = stepStrategy axioms

simpleRule
    :: (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> CommonPureMLPatternSimplifier level
    -- ^ Map from symbol IDs to defined functions
    -> Prim (AxiomPattern level)
    -> (CommonExpandedPattern level, StepProof level)
    -- ^ Configuration being rewritten and its accompanying proof
    -> Simplifier [(CommonExpandedPattern level, StepProof level)]
simpleRule tools simplifier =
    \case
        Builtin -> \(config, proof) ->
            do
                (configs, proof') <-
                    ExpandedPattern.simplify tools simplifier config
                let
                    proof'' = proof <> simplificationProof proof'
                    prove config' = (config', proof'')
                    -- Filter out ⊥ patterns
                    nonEmptyConfigs = ExpandedPattern.filterOr configs
                return (prove <$> toList nonEmptyConfigs)
        Axiom a -> \(config, proof) ->
            do
                case stepWithAxiom tools config a of
                    Left _ -> pure []
                    Right apply -> do
                        (config', proof') <- apply
                        if ExpandedPattern.isBottom config'
                            then return []
                            else return [(config', proof <> proof')]

simpleStrategy
    :: MetaOrObject level
    => [AxiomPattern level]
    -> Strategy (Prim (AxiomPattern level))
simpleStrategy axioms =
    Strategy.many applyAxioms Strategy.stuck
  where
    applyAxioms next = Strategy.all (axiomStep <$> axioms <*> pure next)

simpleStepper
    :: (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> CommonPureMLPatternSimplifier level
    -- ^ Map from symbol IDs to defined functions
    -> [AxiomPattern level]
    -- ^ Rewriting axioms
    -> Limit Natural
    -- ^ The maximum number of steps to be made
    -> (CommonExpandedPattern level, StepProof level)
    -- ^ Configuration being rewritten and its accompanying proof
    -> Simplifier (CommonExpandedPattern level, StepProof level)
simpleStepper tools simplifier axioms stepLimit =
    (<$>) Strategy.pickLongest . runStrategy rule strategy stepLimit
  where
    rule = simpleRule tools simplifier
    strategy = simpleStrategy axioms

{- | A strategy primitive: a rewrite axiom or builtin simplification step.
 -}
data Prim axiom = Builtin | Axiom !axiom

-- | Apply the axiom.
axiom :: axiom -> Prim axiom
axiom = Axiom

-- | Apply builtin simplification.
builtin :: Prim axiom
builtin = Builtin
