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
    , allAxioms
    , anyAxiom
    , heatingCooling
      -- * Re-exports
    , AxiomPattern
    , Natural
    , Strategy
    , pickLongest
    , pickFinal
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

import           Kore.AST.Common
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( MetaOrObject )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.AxiomPatterns
                 ( isCoolingRule, isHeatingRule, isNormalRule )
import           Kore.Step.BaseStep
                 ( AxiomPattern, StepProof (..), simplificationProof,
                 stepWithAxiom )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.OrOfExpandedPattern as ExpandedPattern
import           Kore.Step.Simplification.Data
                 ( CommonPureMLPatternSimplifier,
                 PredicateSubstitutionSimplifier, Simplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Strategy
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
evaluator are applied (see 'ExpandedPattern.simplify' for details).

 -}
axiomStep :: axiom -> Strategy (Prim axiom)
axiomStep a =
    Strategy.sequence [Strategy.apply (axiom a), Strategy.apply simplify]

{- | Transition rule for primitive strategies in 'Prim'.

@transitionRule@ is intended to be partially applied and passed to
'Strategy.runStrategy'.
 -}
transitionRule
    :: (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> CommonPureMLPatternSimplifier level
    -- ^ Evaluates functions in patterns
    -> Prim (AxiomPattern level)
    -> (CommonExpandedPattern level, StepProof level Variable)
    -- ^ Configuration being rewritten and its accompanying proof
    -> Simplifier [(CommonExpandedPattern level, StepProof level Variable)]
transitionRule tools substitutionSimplifier simplifier =
    \case
        Simplify -> transitionSimplify
        Axiom a -> transitionAxiom a
  where
    transitionSimplify (config, proof) =
        do
            (configs, proof') <-
                ExpandedPattern.simplify
                    tools substitutionSimplifier simplifier config
            let
                proof'' = proof <> simplificationProof proof'
                prove config' = (config', proof'')
                -- Filter out ⊥ patterns
                nonEmptyConfigs = ExpandedPattern.filterOr configs
            return (prove <$> toList nonEmptyConfigs)
    transitionAxiom a (config, proof) = do
        result <- runExceptT
            $ stepWithAxiom tools substitutionSimplifier config a
        case result of
            Left _ -> pure []
            Right (config', proof') ->
                if ExpandedPattern.isBottom config'
                    then return []
                    else return [(config', proof <> proof')]

{- | A strategy that applies all the axioms in parallel.

After each successful axiom, the built-in simplification rules and function
evaluator are applied (see 'ExpandedPattern.simplify' for details).

See also: 'Strategy.all'

 -}
allAxioms
    :: [axiom]
    -> Strategy (Prim axiom)
allAxioms axioms =
    Strategy.all (axiomStep <$> axioms)

{- | A strategy that applies the axioms until one succeeds.

The axioms are attempted in order until one succeeds. After a successful axiom,
the built-in simplification rules and function evaluator are applied (see
'ExpandedPattern.simplify' for details).

See also: 'Strategy.any'

 -}
anyAxiom
    :: [axiom]
    -> Strategy (Prim axiom)
anyAxiom axioms =
    Strategy.any (axiomStep <$> axioms)

{- | Heat the configuration, apply a normal rule, and cool the result.
 -}
-- TODO (thomas.tuegel): This strategy is not right because heating/cooling
-- rules must have side conditions if encoded as \rewrites, or they must be
-- \equals rules, which are not handled by this strategy.
heatingCooling
    :: (forall axiom. [axiom] -> Strategy (Prim axiom))
    -- ^ 'allAxioms' or 'anyAxiom'
    -> [AxiomPattern level]
    -> Strategy (Prim (AxiomPattern level))
heatingCooling axiomStrategy axioms =
    Strategy.sequence [Strategy.many heat, normal, Strategy.try cool]
  where
    heatingRules = filter isHeatingRule axioms
    heat = axiomStrategy heatingRules
    normalRules = filter isNormalRule axioms
    normal = axiomStrategy normalRules
    coolingRules = filter isCoolingRule axioms
    cool = axiomStrategy coolingRules
