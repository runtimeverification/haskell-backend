{-|
Module      : Kore.OnePath.Verification
Description : One-path verification
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com

This should be imported qualified.
-}

module Kore.Strategies.Verification
    ( Claim
    , CommonProofState
    , ProofStrategy (..)
    , defaultProofStrategy
    , verify
    , verifyOnePathClaimStep
    , toRulePattern
    , toRule
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

import           Kore.Debug
import           Kore.Internal.Pattern
                 ( Pattern )
import           Kore.Step.Rule as RulePattern
                 ( RulePattern (..) )
import           Kore.Step.Simplification.Simplify
import           Kore.Step.Strategy
import           Kore.Step.Transition
                 ( runTransitionT )
import qualified Kore.Step.Transition as Transition
import           Kore.Strategies.Goal
import           Kore.Strategies.ProofState
                 ( ProofState (Goal) )
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

type CommonProofState = ProofState (Pattern Variable)

{- | Class type for claim-like rules
-}
type Claim claim =
    ( Coercible (RulePattern Variable) claim
    , Coercible (Rule claim) (RulePattern Variable)
    , Coercible (RulePattern Variable) (Rule claim)
    , Coercible claim (RulePattern Variable)
    , Unparse claim
    , Unparse (Rule claim)
    , Goal claim
    )

{- | @Verifer a@ is a 'Simplifier'-based action which returns an @a@.

The action may throw an exception if the proof fails; the exception is a single
@'Pattern' 'Variable'@, the first unprovable configuration.

 -}
type Verifier m = ExceptT (Pattern Variable) m

{- | Verifies a set of claims. When it verifies a certain claim, after the
first step, it also uses the claims as axioms (i.e. it does coinductive proofs).

If the verification fails, returns an error containing a pattern that could
not be rewritten (either because no axiom could be applied or because we
didn't manage to verify a claim within the its maximum number of steps.

If the verification succeeds, it returns ().
-}

verify
    :: forall claim m
    .  Claim claim
    => Show claim
    => Show (Rule claim)
    => MonadSimplify m
    => [Strategy (Prim (Rule claim))]
    -- ^ Creates a one-step strategy from a target pattern. See
    -- 'defaultStrategy'.
    -> [(claim, Limit Natural)]
    -- ^ List of claims, together with a maximum number of verification steps
    -- for each.
    -> ExceptT (Pattern Variable) m ()
verify strategy =
    mapM_ (verifyClaim strategy)

{- | Default implementation for a one-path strategy. You can apply it to the
first two arguments and pass the resulting function to 'verify'.

Things to note when implementing your own:

1. The first step does not use the reachability claims

2. You can return an infinite list.
-}

defaultProofStrategy
    :: forall claim
    .  Claim claim
    => ProofStrategy
    -> [claim]
    -- The claims that we want to prove
    -> [Rule claim]
    -> [Strategy (Prim (Rule claim))]
defaultProofStrategy proofStrategy claims axioms =
    makeProofStrategy
        proofStrategy
        coinductiveRewrites
        rewrites
  where
    rewrites :: [Rule claim]
    rewrites = axioms
    coinductiveRewrites :: [Rule claim]
    coinductiveRewrites = map (toRule . toRulePattern) claims

verifyClaim
    :: forall claim m
    .  MonadSimplify m
    => Claim claim
    => Show claim
    => Show (Rule claim)
    => [Strategy (Prim (Rule claim))]
    -> (claim, Limit Natural)
    -> ExceptT (Pattern Variable) m ()
verifyClaim
    strategy
    (goal, stepLimit)
  = traceExceptT D_OnePath_verifyClaim [debugArg "rule" goal] $ do
    let
        startPattern = Goal $ getConfiguration goal
        destination = getDestination goal
        limitedStrategy =
            Limit.takeWithin
                stepLimit
                strategy
    executionGraph <-
        runStrategy (modifiedTransitionRule destination) limitedStrategy startPattern
    -- Throw the first unproven configuration as an error.
    Foldable.traverse_ Monad.Except.throwError (unprovenNodes executionGraph)
  where
    modifiedTransitionRule
        :: Pattern Variable
        -> Prim (Rule claim)
        -> CommonProofState
        -> TransitionT (Rule claim) (Verifier m) CommonProofState
    modifiedTransitionRule destination prim proofState' = do
        transitions <-
            Monad.Trans.lift . Monad.Trans.lift . runTransitionT
            $ transitionRule' destination prim proofState'
        Transition.scatter transitions

-- | Attempts to perform a single proof step, starting at the configuration
-- in the execution graph designated by the provided node. Re-constructs the
-- execution graph by inserting this step.
verifyClaimStep
    :: forall claim m
    .  MonadSimplify m
    => Claim claim
    => ProofStrategy
    -> claim
    -- ^ claim that is being proven
    -> [claim]
    -- ^ list of claims in the spec module
    -> [Rule claim]
    -- ^ list of axioms in the main module
    -> ExecutionGraph CommonProofState (Rule claim)
    -- ^ current execution graph
    -> Graph.Node
    -- ^ selected node in the graph
    -> m (ExecutionGraph CommonProofState (Rule claim))
verifyClaimStep
    proofStrategy
    target
    claims
    axioms
    eg@ExecutionGraph { root }
    node
  = do
      let destination = getDestination target
      executionHistoryStep
        (transitionRule' destination)
        strategy'
        eg
        node
  where
    strategy' :: Strategy (Prim (Rule claim))
    strategy'
      | isRoot =
          firstStepStrategy proofStrategy rewrites
      | otherwise =
          nextStepStrategy
            proofStrategy
            coinductiveRewrites
            rewrites

    rewrites :: [Rule claim]
    rewrites = axioms

    coinductiveRewrites :: [Rule claim]
    coinductiveRewrites = coerce . toRulePattern <$> claims

    isRoot :: Bool
    isRoot = node == root

verifyOnePathClaimStep
    :: forall claim m
    .  MonadSimplify m
    => Claim claim
    => claim
    -- ^ claim that is being proven
    -> [claim]
    -- ^ list of claims in the spec module
    -> [Rule claim]
    -- ^ list of axioms in the main module
    -> ExecutionGraph CommonProofState (Rule claim)
    -- ^ current execution graph
    -> Graph.Node
    -- ^ selected node in the graph
    -> m (ExecutionGraph CommonProofState (Rule claim))
verifyOnePathClaimStep = verifyClaimStep OnePathStrategy

transitionRule'
    :: forall claim m
    .  MonadSimplify m
    => Claim claim
    => Pattern Variable
    -> Prim (Rule claim)
    -> CommonProofState
    -> TransitionT (Rule claim) m CommonProofState
transitionRule' destination prim state = do
    let goal = flip makeRuleFromPatterns destination <$> state
    next <- transitionRule prim goal
    pure $ fmap getConfiguration next

toRulePattern
    :: forall claim
    .  Claim claim
    => claim -> RulePattern Variable
toRulePattern = coerce

toRule
    :: forall claim
    .  Claim claim
    => RulePattern Variable -> Rule claim
toRule = coerce
