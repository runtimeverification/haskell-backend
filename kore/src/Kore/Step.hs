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

import Control.Error
    ( runExceptT
    )
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
import Kore.Syntax.Variable
import qualified Kore.Unification.Procedure as Unification
import Kore.Unparser
import qualified Pretty


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

{- | Transition rule for primitive strategies in 'Prim'.

@transitionRule@ is intended to be partially applied and passed to
'Strategy.runStrategy'.
 -}
transitionRule
    :: forall m
    .  HasCallStack
    => MonadSimplify m
    => Prim (RewriteRule VariableName)
    -> Pattern VariableName
    -- ^ Configuration being rewritten
    -> TransitionT (RewriteRule VariableName) m (Pattern VariableName)
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
        eitherResults <-
            Step.applyRewriteRulesParallel
                Unification.unificationProcedure
                [mkRewritingRule rule]
                config
            & lift . runExceptT
        case eitherResults of
            Left err ->
                (error . show . Pretty.vsep)
                    [ "Could not apply the axiom:"
                    , unparse rule
                    , "to the configuration:"
                    , unparse config
                    , "Un-implemented unification case; aborting execution."
                    , "err=" <> Pretty.pretty err
                    ]
            Right results ->
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
    :: From rewrite (Attribute.Priority, Attribute.Owise)
    => [rewrite]
    -> Strategy (Prim rewrite)
priorityAllStrategy rewrites =
    Strategy.first (fmap allRewrites priorityGroups)
  where
    priorityGroups = groupSortOn Attribute.getPriorityOfAxiom rewrites

priorityAnyStrategy
    :: From rewrite (Attribute.Priority, Attribute.Owise)
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
    :: ([RewriteRule VariableName] -> Strategy (Prim (RewriteRule VariableName)))
    -- ^ 'allRewrites' or 'anyRewrite'
    -> [RewriteRule VariableName]
    -> Strategy (Prim (RewriteRule VariableName))
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
