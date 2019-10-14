{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com

This should be imported qualified.
-}

module Kore.Strategies.Verification
    ( Claim
    , CommonProofState
    , verify
    , verifyClaimStep
    , toRulePattern
    , toRule
    ) where

import Control.Monad.Catch
    ( MonadCatch
    )
import Control.Monad.Except
    ( ExceptT
    )
import qualified Control.Monad.Except as Monad.Except
import qualified Control.Monad.Trans as Monad.Trans
import Data.Coerce
    ( Coercible
    , coerce
    )
import qualified Data.Foldable as Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import Data.Limit
    ( Limit
    )
import qualified Data.Limit as Limit

import Kore.Debug
import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Step.Rule as RulePattern
    ( OnePathRule
    , RulePattern (..)
    )
import Kore.Step.Simplification.Simplify
import Kore.Step.Strategy
import Kore.Step.Transition
    ( runTransitionT
    )
import qualified Kore.Step.Transition as Transition
import Kore.Strategies.Goal
import qualified Kore.Strategies.ProofState as ProofState
import Kore.Syntax.Variable
    ( Variable
    )
import Kore.Unparser
import Numeric.Natural
    ( Natural
    )

type CommonProofState = ProofState (OnePathRule Variable) (Pattern Variable)

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
    , Prim claim ~ ProofState.Prim (Rule claim)
    , ProofState claim claim ~ ProofState.ProofState claim
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
    => ProofState claim (Pattern Variable) ~ CommonProofState
    => Show claim
    => Show (Rule claim)
    => (MonadCatch m, MonadSimplify m)
    => [Strategy (Prim claim)]
    -> [(claim, Limit Natural)]
    -- ^ List of claims, together with a maximum number of verification steps
    -- for each.
    -> ExceptT (Pattern Variable) m ()
verify strategy' =
    mapM_ (verifyClaim strategy')

verifyClaim
    :: forall claim m
    .  (MonadCatch m, MonadSimplify m)
    => ProofState claim (Pattern Variable) ~ CommonProofState
    => Claim claim
    => Show claim
    => Show (Rule claim)
    => [Strategy (Prim claim)]
    -> (claim, Limit Natural)
    -> ExceptT (Pattern Variable) m ()
verifyClaim
    strategy'
    (goal, stepLimit)
  = traceExceptT D_OnePath_verifyClaim [debugArg "rule" goal] $ do
    let
        startPattern = ProofState.Goal $ getConfiguration goal
        destination = getDestination goal
        limitedStrategy =
            Limit.takeWithin
                stepLimit
                strategy'
    executionGraph <-
        runStrategy (modifiedTransitionRule destination) limitedStrategy startPattern
    -- Throw the first unproven configuration as an error.
    Foldable.traverse_ Monad.Except.throwError (unprovenNodes executionGraph)
  where
    modifiedTransitionRule
        :: Pattern Variable
        -> Prim claim
        -> CommonProofState
        -> TransitionT (Rule claim) (Verifier m) CommonProofState
    modifiedTransitionRule destination prim proofState' = do
        transitions <-
            Monad.Trans.lift . Monad.Trans.lift . runTransitionT
            $ transitionRule' destination prim proofState'
        Transition.scatter transitions

-- TODO(Ana): allow running with all-path strategy steps
-- when the REPL will be connected to all-path
-- | Attempts to perform a single proof step, starting at the configuration
-- in the execution graph designated by the provided node. Re-constructs the
-- execution graph by inserting this step.
verifyClaimStep
    :: forall claim m
    .  (MonadCatch m, MonadSimplify m)
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
verifyClaimStep
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
    strategy' :: Strategy (Prim claim)
    strategy'
        | isRoot =
            onePathFirstStep rewrites
        | otherwise =
            onePathFollowupStep
                (coerce . toRulePattern <$> claims)
                rewrites

    rewrites :: [Rule claim]
    rewrites = axioms

    isRoot :: Bool
    isRoot = node == root

transitionRule'
    :: forall claim m
    .  (MonadCatch m, MonadSimplify m)
    => Claim claim
    => Pattern Variable
    -> Prim claim
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
