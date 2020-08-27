{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

Strategy-based interface to rule application (step-wise execution).

 -}

module Kore.Step
    ( -- * Primitive strategies
      Prim (..)
    , rewrite
    , simplify
    , rewriteStep
    , priorityAllStrategy
    , priorityAnyStrategy
    , TransitionRule
    , transitionRule
    , heatingCooling
      -- * Re-exports
    , RulePattern
    , Natural
    , Strategy
    , pickLongest
    , pickFinal
    , runStrategy
    ) where

import Prelude.Kore

import qualified Data.Foldable as Foldable
import Data.List.Extra
    ( groupSortOn
    , sortOn
    )
import Numeric.Natural
    ( Natural
    )

import qualified Kore.Attribute.Axiom as Attribute
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Rewriting.RewritingVariable
import qualified Kore.Step.RewriteStep as Step
import Kore.Step.RulePattern
    ( RewriteRule (..)
    , RulePattern
    , isCoolingRule
    , isHeatingRule
    , isNormalRule
    )
import qualified Kore.Step.Simplification.Pattern as Pattern
    ( simplifyTopConfiguration
    )
import Kore.Step.Simplification.Simplify as Simplifier
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
    ( filterMultiOr
    )
import qualified Kore.Step.Step as Step
import Kore.Step.Strategy hiding
    ( transitionRule
    )
import qualified Kore.Step.Strategy as Strategy
import qualified Kore.Step.Transition as Transition
import qualified Kore.Unification.Procedure as Unification

{- | A strategy primitive: a rewrite rule or builtin simplification step.
 -}
data Prim rewrite = Simplify | Rewrite !rewrite
    deriving (Show)

-- | Apply the rewrite.
rewrite :: rewrite -> Prim rewrite
rewrite = Rewrite

-- | Apply builtin simplification rewrites and evaluate functions.
simplify :: Prim rewrite
simplify = Simplify

{- | A single-step strategy which applies the given rewrite rule.

If the rewrite is successful, the built-in simplification rules and function
evaluator are applied (see 'Pattern.simplify' for details).

 -}
rewriteStep :: rewrite -> Strategy (Prim rewrite)
rewriteStep a =
    Strategy.sequence [Strategy.apply (rewrite a), Strategy.apply simplify]

{- | @TransitionRule@ is the general type of transition rules over 'Prim'.
 -}
type TransitionRule monad rule state =
    Prim rule -> state -> Strategy.TransitionT rule monad state

{- | Transition rule for primitive strategies in 'Prim'.

@transitionRule@ is intended to be partially applied and passed to
'Strategy.runStrategy'.
 -}
transitionRule
    ::  forall simplifier
    .   MonadSimplify simplifier
    =>  TransitionRule simplifier
            (RewriteRule RewritingVariableName)
            (Pattern RewritingVariableName)
transitionRule =
    \case
        Simplify -> transitionSimplify
        Rewrite a -> transitionRewrite a
  where
    transitionSimplify config = do
        configs <- lift $ Pattern.simplifyTopConfiguration config
        filteredConfigs <- SMT.Evaluator.filterMultiOr configs
        Foldable.asum (pure <$> filteredConfigs)
    transitionRewrite rule config = do
        Transition.addRule rule
        results <-
            Step.applyRewriteRulesParallel
                Unification.unificationProcedure
                [rule]
                config
            & lift
        Foldable.asum
            (pure <$> Step.gatherResults results)


{- | A strategy that applies all the rewrites in parallel.

After each successful rewrite, the built-in simplification rules and function
evaluator are applied (see 'Pattern.simplify' for details).

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
(see 'Pattern.simplify' for details).

See also: 'Strategy.any'

 -}
anyRewrite
    :: [rewrite]
    -> Strategy (Prim rewrite)
anyRewrite rewrites =
    Strategy.any (rewriteStep <$> rewrites)

priorityAllStrategy
    :: From rewrite Attribute.PriorityAttributes
    => [rewrite]
    -> Strategy (Prim rewrite)
priorityAllStrategy rewrites =
    Strategy.first (fmap allRewrites priorityGroups)
  where
    priorityGroups = groupSortOn Attribute.getPriorityOfAxiom rewrites

priorityAnyStrategy
    :: From rewrite Attribute.PriorityAttributes
    => [rewrite]
    -> Strategy (Prim rewrite)
priorityAnyStrategy rewrites =
    anyRewrite sortedRewrites
  where
    sortedRewrites = sortOn Attribute.getPriorityOfAxiom rewrites

{- | Heat the configuration, apply a normal rewrite, and cool the result.
 -}
-- TODO (thomas.tuegel): This strategy is not right because heating/cooling
-- rules must have side conditions if encoded as \rewrites, or they must be
-- \equals rules, which are not handled by this strategy.
heatingCooling
    :: From rule Attribute.HeatCool
    => ([rule] -> Strategy (Prim rule))
    -- ^ 'allRewrites' or 'anyRewrite'
    -> [rule]
    -> Strategy (Prim rule)
heatingCooling rewriteStrategy rewrites =
    Strategy.sequence [Strategy.many heat, normal, Strategy.try cool]
  where
    heatingRules = filter isHeatingRule rewrites
    heat = rewriteStrategy heatingRules
    normalRules = filter isNormalRule rewrites
    normal = rewriteStrategy normalRules
    coolingRules = filter isCoolingRule rewrites
    cool = rewriteStrategy coolingRules
