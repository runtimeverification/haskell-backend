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
    ( -- * Primitive strategies
      Prim (..)
    , axiom
    , builtin
    , axiomStep
    , transitionRule
    , stepStrategy
    , simpleStrategy
    , defaultStrategy
      -- * Re-exports
    , Limit (..)
    , Natural
    , Strategy
    , pickLongest
    , pickStuck
    , runStrategy
    ) where

import Data.Foldable
       ( toList )
import Data.Semigroup
       ( (<>) )
import Numeric.Natural ( Natural )

import Kore.AST.MetaOrObject
       ( MetaOrObject )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools )
import Kore.Step.BaseStep
       ( AxiomPattern, StepProof (..), simplificationProof, stepWithAxiom )

import           Kore.Step.AxiomPatterns
                 ( isCoolingRule, isHeatingRule, isNormalRule )
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
                 ( Limit (..), Strategy, pickLongest, pickStuck, runStrategy )
import qualified Kore.Step.Strategy as Strategy

{- | A strategy primitive: a rewrite axiom or builtin simplification step.
 -}
data Prim axiom = Builtin | Axiom !axiom

-- | Apply the axiom.
axiom :: axiom -> Prim axiom
axiom = Axiom

-- | Apply builtin simplification.
builtin :: Prim axiom
builtin = Builtin

{- | A single-step strategy which applies the given axiom.

  If the axiom is successful, the builtin simplifier is applied. The combination
  of axiom and builtin simplifier is considered one step for the purposes of the
  step limit.

 -}
axiomStep :: axiom -> Strategy (Prim axiom) -> Strategy (Prim axiom)
axiomStep a =
    Strategy.step . Strategy.apply (axiom a) . Strategy.apply builtin

{- |
    Transition rule for primitive strategies in 'Prim'.

    @transitionRule@ is intended to be partially applied and passed to
    'Strategy.runStrategy'.
 -}
transitionRule
    :: (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> CommonPureMLPatternSimplifier level
    -- ^ Map from symbol IDs to defined functions
    -> Prim (AxiomPattern level)
    -> (CommonExpandedPattern level, StepProof level)
    -- ^ Configuration being rewritten and its accompanying proof
    -> Simplifier [(CommonExpandedPattern level, StepProof level)]
transitionRule tools simplifier =
    \case
        Builtin -> transitionBuiltin
        Axiom a -> transitionAxiom a
  where
    transitionBuiltin (config, proof) =
        do
            (configs, proof') <-
                ExpandedPattern.simplify tools simplifier config
            let
                proof'' = proof <> simplificationProof proof'
                prove config' = (config', proof'')
                -- Filter out ⊥ patterns
                nonEmptyConfigs = ExpandedPattern.filterOr configs
            return (prove <$> toList nonEmptyConfigs)
    transitionAxiom a (config, proof) =
        case stepWithAxiom tools config a of
            Left _ -> pure []
            Right apply -> do
                (config', proof') <- apply
                if ExpandedPattern.isBottom config'
                    then return []
                    else return [(config', proof <> proof')]

{- | A strategy which takes one step by attempting all the axioms.

  The builtin simplifier is used after each successful axiom step. The
  combination of axiom and builtin simplification is considered one step for the
  purposes of the step limit.

 -}
stepStrategy
    :: MetaOrObject level
    => [AxiomPattern level]
    -> Strategy (Prim (AxiomPattern level))
stepStrategy axioms =
    Strategy.all (applyAxiom <$> axioms)
  where
    applyAxiom a = axiomStep a Strategy.stuck

{- | A strategy which applies all the given axioms as many times as possible.

  The builtin simplifier is used after each successful axiom step. The
  combination of axiom and builtin simplification is considered one step for the
  purposes of the step limit.

 -}
simpleStrategy
    :: MetaOrObject level
    => [AxiomPattern level]
    -> Strategy (Prim (AxiomPattern level))
simpleStrategy axioms =
    Strategy.many applyAxioms Strategy.stuck
  where
    applyAxioms next = Strategy.all (axiomStep <$> axioms <*> pure next)

{- | Heat the configuration, apply a normal rule, and cool the result.
 -}
defaultStrategy
    :: MetaOrObject level
    => [AxiomPattern level]
    -> Strategy (Prim (AxiomPattern level))
defaultStrategy axioms =
    Strategy.many (Strategy.many heatingCoolingCycle) Strategy.stuck
  where
    heatingCoolingCycle = Strategy.many heat . normal . cool
    heatingRules = filter isHeatingRule axioms
    heat next = Strategy.all (axiomStep <$> heatingRules <*> pure next)
    normalRules = filter isNormalRule axioms
    normal next = Strategy.all (axiomStep <$> normalRules <*> pure next)
    coolingRules = filter isCoolingRule axioms
    cool next = Strategy.all (axiomStep <$> coolingRules <*> pure next)
