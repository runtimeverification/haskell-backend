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

import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import qualified Data.Text.Prettyprint.Doc as Pretty
import           GHC.Stack
                 ( HasCallStack )
import           Numeric.Natural
                 ( Natural )

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.Pattern
                 ( Pattern )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Result as Result
                 ( mergeResults )
import           Kore.Step.Rule
                 ( RewriteRule (RewriteRule), RulePattern, isCoolingRule,
                 isHeatingRule, isNormalRule )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier )
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplify )
import qualified Kore.Step.Step as Step
import           Kore.Step.Strategy
import qualified Kore.Step.Strategy as Strategy
import qualified Kore.Step.Transition as Transition
import           Kore.Syntax.Variable
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser


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
    :: HasCallStack
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions in patterns
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from symbol IDs to defined functions
    -> Prim (RewriteRule Variable)
    -> Pattern Variable
    -- ^ Configuration being rewritten and its accompanying proof
    -> TransitionT (RewriteRule Variable) Simplifier (Pattern Variable)
transitionRule tools substitutionSimplifier simplifier axiomIdToSimplifier =
    \case
        Simplify -> transitionSimplify
        Rewrite a -> transitionRewrite a
  where
    transitionSimplify config =
        do
            configs <-
                Monad.Trans.lift
                $ Pattern.simplify
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToSimplifier
                    config
            let
                -- Filter out ⊥ patterns
                nonEmptyConfigs = MultiOr.filterOr configs
            Foldable.asum (pure <$> nonEmptyConfigs)
    transitionRewrite rule config = do
        Transition.addRule rule
        eitherResults <-
            Monad.Trans.lift
            $ Monad.Unify.runUnifier
            $ Step.applyRewriteRules
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                (Step.UnificationProcedure Unification.unificationProcedure)
                [rule]
                config
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
                    (pure <$> Step.gatherResults (Result.mergeResults results))


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

{- | Heat the configuration, apply a normal rewrite, and cool the result.
 -}
-- TODO (thomas.tuegel): This strategy is not right because heating/cooling
-- rules must have side conditions if encoded as \rewrites, or they must be
-- \equals rules, which are not handled by this strategy.
heatingCooling
    :: (forall rewrite. [rewrite] -> Strategy (Prim rewrite))
    -- ^ 'allRewrites' or 'anyRewrite'
    -> [RewriteRule Variable]
    -> Strategy (Prim (RewriteRule Variable))
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
