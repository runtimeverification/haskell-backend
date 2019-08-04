{-|
Module      : Kore.OnePath.Verification
Description : One-path verification
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com

This should be imported qualified.
-}

module Kore.OnePath.Verification
    ( Axiom (..)
    , Claim
    , isTrusted
    , defaultStrategy
    , verify
    , verifyClaimStep
    ) where

import           Control.Monad.Except
                 ( ExceptT )
import qualified Control.Monad.Except as Monad.Except
import qualified Control.Monad.Trans as Monad.Trans
import           Data.Coerce
                 ( Coercible, coerce )
import qualified Data.Foldable as Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import           Data.Limit
                 ( Limit )
import qualified Data.Limit as Limit
import           Data.Maybe

import qualified Kore.Attribute.Axiom as Attribute
import qualified Kore.Attribute.Trusted as Trusted
import           Kore.Debug
import           Kore.Goal
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.Pattern
                 ( Conditional (Conditional), Pattern )
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.Pattern as Conditional
                 ( Conditional (..) )
import           Kore.Step.Rule
                 ( OnePathRule (..), RewriteRule (RewriteRule),
                 RulePattern (RulePattern) )
import           Kore.Step.Rule as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Simplification.Data
import           Kore.Step.Strategy
import           Kore.Step.Transition
                 ( runTransitionT )
import qualified Kore.Step.Transition as Transition
import           Kore.Syntax.Variable
                 ( Variable )
import           Kore.Unparser
import           Numeric.Natural
                 ( Natural )

{- NOTE: Non-deterministic semantics

The current implementation of one-path verification assumes that the proof goal
is deterministic, that is: the proof goal would not be discharged during at a
non-confluent state in the execution of a non-deterministic semantics. (Often
this means that the definition is simply deterministic.) As a result, given the
non-deterministic definition

> module ABC
>   import DOMAINS
>   syntax S ::= "a" | "b" | "c"
>   rule [ab]: a => b
>   rule [ac]: a => c
> endmodule

this claim would be provable,

> rule a => b [claim]

but this claim would **not** be provable,

> rule a => c [claim]

because the algorithm would first apply semantic rule [ab], which prevents rule
[ac] from being used.

We decided to assume that the definition is deterministic because one-path
verification is mainly used only for deterministic semantics and the assumption
simplifies the implementation. However, this assumption is not an essential
feature of the algorithm. You should not rely on this assumption elsewhere. This
decision is subject to change without notice.

 -}

{- | Class type for claim-like rules
-}
type Claim claim =
    ( Coercible (RulePattern Variable) claim
    , Coercible claim (RulePattern Variable)
    , Unparse claim
    )

-- | Is the 'Claim' trusted?
isTrusted :: Claim claim => claim -> Bool
isTrusted =
    Trusted.isTrusted
    . Attribute.trusted
    . RulePattern.attributes
    . coerce

{- | Wrapper for a rewrite rule that should be used as an axiom.
-}
newtype Axiom = Axiom
    { unAxiom :: RewriteRule Variable
    }

{- | @Verifer a@ is a 'Simplifier'-based action which returns an @a@.

The action may throw an exception if the proof fails; the exception is a single
@'Pattern' 'Variable'@, the first unprovable configuration.

 -}
type Verifier m = ExceptT (OnePathRule Variable) m

{- | Verifies a set of claims. When it verifies a certain claim, after the
first step, it also uses the claims as axioms (i.e. it does coinductive proofs).

If the verification fails, returns an error containing a pattern that could
not be rewritten (either because no axiom could be applied or because we
didn't manage to verify a claim within the its maximum number of steps.

If the verification succeeds, it returns ().
-}
verify
    :: forall m
    .  MonadSimplify m
    =>  (  OnePathRule Variable
        -> [Strategy
            (Prim (RewriteRule Variable)
            )
           ]
        )
    -- ^ Creates a one-step strategy from a target pattern. See
    -- 'defaultStrategy'.
    -> [(OnePathRule Variable, Limit Natural)]
    -- ^ List of claims, together with a maximum number of verification steps
    -- for each.
    -> ExceptT (OnePathRule Variable) m ()
verify strategyBuilder =
    mapM_ (verifyClaim strategyBuilder)

verifyClaim
    :: forall m
    .  MonadSimplify m
    =>  (  OnePathRule Variable
        -> [Strategy (Prim (RewriteRule Variable))]
        )
    -> (OnePathRule Variable, Limit Natural)
    -> ExceptT (OnePathRule Variable) m ()
verifyClaim
    strategyBuilder
    (rule@(OnePathRule RulePattern {left, right, requires, ensures}), stepLimit)
  = traceExceptT D_OnePath_verifyClaim [debugArg "rule" rule] $ do
    let
        strategy =
            Limit.takeWithin
                stepLimit
                (strategyBuilder rule)
        startPattern :: ProofState (OnePathRule Variable)
        startPattern =
                Goal rule

    executionGraph <- runStrategy transitionRule' strategy startPattern
    -- Throw the first unproven configuration as an error.
    -- This might appear to be unnecessary because transitionRule' (below)
    -- throws an error if it encounters a Stuck proof state. However, the proof
    -- could also fail because the depth limit was reached, yet we never
    -- encountered a Stuck state.
    Foldable.traverse_ Monad.Except.throwError (unprovenNodes executionGraph)
  where
    transitionRule'
        :: Prim (RewriteRule Variable)
        -> ProofState (OnePathRule Variable)
        -> TransitionT (RewriteRule Variable) (Verifier m) (ProofState (OnePathRule Variable))
    transitionRule' prim proofState = do
        transitions <-
            Monad.Trans.lift . Monad.Trans.lift . runTransitionT
            $ transitionRule prim proofState
        let (configs, _) = unzip transitions
            stuckConfigs = mapMaybe extractUnproven configs
        Foldable.traverse_ Monad.Except.throwError stuckConfigs
        Transition.scatter transitions

-- | Attempts to perform a single proof step, starting at the configuration
-- in the execution graph designated by the provided node. Re-constructs the
-- execution graph by inserting this step.
verifyClaimStep
    :: MonadSimplify m
    => OnePathRule Variable
    -- ^ claim that is being proven
    -> [OnePathRule Variable]
    -- ^ list of claims in the spec module
    -> [RewriteRule Variable]
    -- ^ list of axioms in the main module
    -> ExecutionGraph (ProofState (OnePathRule Variable)) (RewriteRule Variable)
    -- ^ current execution graph
    -> Graph.Node
    -- ^ selected node in the graph
    -> m (ExecutionGraph (ProofState (OnePathRule Variable)) (RewriteRule Variable))
verifyClaimStep
    target
    claims
    axioms
    eg@ExecutionGraph { root }
    node
  = executionHistoryStep
        transitionRule'
        strategy'
        eg
        node
  where
    transitionRule'
        :: Prim (Rule goal)
        -> ProofState goal
        -> TransitionT (Rule goal) m (ProofState goal)
    transitionRule' = transitionRule

    strategy' :: Strategy (Prim (RewriteRule Variable))
    strategy'
        | isRoot =
            firstStep
                (RewriteRule . coerce <$> claims)
                axioms
        | otherwise =
            nextStep
                (RewriteRule . coerce <$> claims)
                axioms

    isRoot :: Bool
    isRoot = node == root
