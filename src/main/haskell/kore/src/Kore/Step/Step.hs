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
    , simplify
    , axiomStep
    , transitionRule
    , stepStrategy
    , simpleStrategy
    , defaultStrategy
      -- * Re-exports
    , AxiomPattern
    , Limit (..)
    , Natural
    , Strategy
    , pickLongest
    , pickStuck
    , runStrategy
    ) where

import Control.Monad.Except
       ( runExceptT )
import Data.Foldable
       ( toList )
import Data.Semigroup
       ( (<>) )
import Numeric.Natural
       ( Natural )

import Kore.AST.Common
       ( Variable )
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
data Prim axiom = Simplify | Axiom !axiom

-- | Apply the axiom.
axiom :: axiom -> Prim axiom
axiom = Axiom

-- | Apply builtin simplification rules and evaluate functions.
simplify :: Prim axiom
simplify = Simplify

{- | A single-step strategy which applies the given axiom.

    If the axiom is successful, the built-in simplification rules and function
    evaluator are applied (see 'ExpandedPattern.simplify' for details). The
    combination is considered one step for the purposes of the step limit.

 -}
axiomStep :: axiom -> Strategy (Prim axiom) -> Strategy (Prim axiom)
axiomStep a =
    Strategy.step . Strategy.apply (axiom a) . Strategy.apply simplify

{- |
    Transition rule for primitive strategies in 'Prim'.

    @transitionRule@ is intended to be partially applied and passed to
    'Strategy.runStrategy'.
 -}
transitionRule
    :: (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> CommonPureMLPatternSimplifier level
    -- ^ Evaluates functions in patterns
    -> Prim (AxiomPattern level)
    -> (CommonExpandedPattern level, StepProof Variable level)
    -- ^ Configuration being rewritten and its accompanying proof
    -> Simplifier [(CommonExpandedPattern level, StepProof Variable level)]
transitionRule tools simplifier =
    \case
        Simplify -> transitionSimplify
        Axiom a -> transitionAxiom a
  where
    transitionSimplify (config, proof) =
        do
            (configs, proof') <-
                ExpandedPattern.simplify tools simplifier config
            let
                proof'' = proof <> simplificationProof proof'
                prove config' = (config', proof'')
                -- Filter out ⊥ patterns
                nonEmptyConfigs = ExpandedPattern.filterOr configs
            return (prove <$> toList nonEmptyConfigs)
    transitionAxiom a (config, proof) = do
        result <- runExceptT $ stepWithAxiom tools config a
        case result of
            Left _ -> pure []
            Right (config', proof') ->
                if ExpandedPattern.isBottom config'
                    then return []
                    else return [(config', proof <> proof')]

{- | A strategy which takes one step by attempting all the axioms.

    If the axiom is successful, the built-in simplification rules and function
    evaluator are applied (see 'ExpandedPattern.simplify' for details). The
    combination is considered one step for the purposes of the step limit.

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

    If the axiom is successful, the built-in simplification rules and function
    evaluator are applied (see 'ExpandedPattern.simplify' for details). The
    combination is considered one step for the purposes of the step limit.

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
-- TODO (thomas.tuegel): This strategy is not right because heating/cooling
-- rules must have side conditions if encoded as \rewrites, or they must be
-- \equals rules, which are not handled by this strategy.
defaultStrategy
    :: MetaOrObject level
    => [AxiomPattern level]
    -> Strategy (Prim (AxiomPattern level))
defaultStrategy axioms =
    Strategy.many heatingCoolingCycle Strategy.stuck
  where
    heatingCoolingCycle = Strategy.many heat . normal . Strategy.try cool
    heatingRules = filter isHeatingRule axioms
    heat next = Strategy.all (axiomStep <$> heatingRules <*> pure next)
    normalRules = filter isNormalRule axioms
    normal next = Strategy.all (axiomStep <$> normalRules <*> pure next)
    coolingRules = filter isCoolingRule axioms
    cool next = Strategy.all (axiomStep <$> coolingRules <*> pure next)
