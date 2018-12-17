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
    , rewrite
    , simplify
    , rewriteStep
    , transitionRule
    , allRewrites
    , anyRewrite
    , heatingCooling
      -- * Re-exports
    , RulePattern
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
import Data.Maybe
       ( mapMaybe )
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
                 ( RewriteRule (RewriteRule), RulePattern, isCoolingRule,
                 isHeatingRule, isNormalRule )
import           Kore.Step.BaseStep
                 ( StepProof (..), StepResult (StepResult),
                 simplificationProof, stepWithRule )
import           Kore.Step.BaseStep as StepResult
                 ( StepResult (..) )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.OrOfExpandedPattern as ExpandedPattern
import           Kore.Step.Simplification.Data
                 ( CommonStepPatternSimplifier,
                 PredicateSubstitutionSimplifier, Simplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Strategy
import qualified Kore.Step.Strategy as Strategy

{- | A strategy primitive: a rewrite rule or builtin simplification step.
 -}
data Prim rewrite = Simplify | Rewrite !rewrite

-- | Apply the rewrite.
rewrite :: rewrite -> Prim rewrite
rewrite = Rewrite

-- | Apply builtin simplification rewrites and evaluate functions.
simplify :: Prim rewrite
simplify = Simplify

{- | A single-step strategy which applies the given rewrite rule.

If the rewrite is successful, the built-in simplification rules and function
evaluator are applied (see 'ExpandedPattern.simplify' for details).

 -}
rewriteStep :: rewrite -> Strategy (Prim rewrite)
rewriteStep a =
    Strategy.sequence [Strategy.apply (rewrite a), Strategy.apply simplify]

{- | Transition rule for primitive strategies in 'Prim'.

@transitionRule@ is intended to be partially applied and passed to
'Strategy.runStrategy'.
 -}
transitionRule
    :: (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> CommonStepPatternSimplifier level
    -- ^ Evaluates functions in patterns
    -> Prim (RewriteRule level)
    -> (CommonExpandedPattern level, StepProof level Variable)
    -- ^ Configuration being rewritten and its accompanying proof
    -> Simplifier [(CommonExpandedPattern level, StepProof level Variable)]
transitionRule tools substitutionSimplifier simplifier =
    \case
        Simplify -> transitionSimplify
        Rewrite a -> transitionRewrite a
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
    transitionRewrite a (config, proof) = do
        result <- runExceptT
            $ stepWithRule tools substitutionSimplifier config a
        case result of
            Left _ -> pure []
            Right results -> return $ mapMaybe (patternFromResult proof) results
    patternFromResult
        :: StepProof level Variable
        -> (StepResult level Variable, StepProof level Variable)
        -> Maybe (CommonExpandedPattern level, StepProof level Variable)
    patternFromResult
        proof
        ( StepResult { rewrittenPattern = config' }
        , proof'
        )
      =
        if ExpandedPattern.isBottom config'
            then Nothing
            else Just (config', proof <> proof')


{- | A strategy that applies all the rewrites in parallel.

After each successful rewrite, the built-in simplification rules and function
evaluator are applied (see 'ExpandedPattern.simplify' for details).

See also: 'Strategy.all'

 -}
allRewrites
    :: [rewrite]
    -> Strategy (Prim rewrite)
allRewrites rewrites =
    Strategy.all (rewriteStep <$> rewrites)

{- | A strategy that applies the rewrites until one succeeds.

The rewrites are attempted in order until one succeeds. After a successful
rewrite, the built-in simplification rules and function evaluator are applied
(see 'ExpandedPattern.simplify' for details).

See also: 'Strategy.any'

 -}
anyRewrite
    :: [rewrite]
    -> Strategy (Prim rewrite)
anyRewrite rewrites =
    Strategy.any (rewriteStep <$> rewrites)

{- | Heat the configuration, apply a normal rewrite, and cool the result.
 -}
-- TODO (thomas.tuegel): This strategy is not right because heating/cooling
-- rules must have side conditions if encoded as \rewrites, or they must be
-- \equals rules, which are not handled by this strategy.
heatingCooling
    :: (forall rewrite. [rewrite] -> Strategy (Prim rewrite))
    -- ^ 'allRewrites' or 'anyRewrite'
    -> [RewriteRule level]
    -> Strategy (Prim (RewriteRule level))
heatingCooling rewriteStrategy rewrites =
    Strategy.sequence [Strategy.many heat, normal, Strategy.try cool]
  where
    heatingRules = filter isHeating rewrites
    isHeating (RewriteRule rule) = isHeatingRule rule
    heat = rewriteStrategy heatingRules
    normalRules = filter isNormal rewrites
    isNormal (RewriteRule rule) = isNormalRule rule
    normal = rewriteStrategy normalRules
    coolingRules = filter isCooling rewrites
    isCooling (RewriteRule rule) = isCoolingRule rule
    cool = rewriteStrategy coolingRules
