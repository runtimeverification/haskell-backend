{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com

This should be imported qualified.
-}

module Kore.Strategies.Verification
    ( CommonProofState
    , Stuck (..)
    , AllClaims (..)
    , Axioms (..)
    , ToProve (..)
    , AlreadyProven (..)
    , verify
    , verifyClaimStep
    , lhsProofStateTransformer
    ) where

import Prelude.Kore

import Control.Monad
    ( (>=>)
    )
import qualified Control.Monad as Monad
    ( foldM_
    )
import Control.Monad.Catch
    ( MonadCatch
    , handle
    )
import Control.Monad.Except
    ( ExceptT
    , withExceptT
    )
import qualified Control.Monad.Except as Monad.Except
import qualified Data.Foldable as Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Stream.Infinite as Stream
import Data.Text
    ( Text
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import Numeric.Natural
    ( Natural
    )

import Data.Limit
    ( Limit
    )
import qualified Data.Limit as Limit
import Kore.Debug
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Profiler.Profile as Profile
import Kore.Step.RulePattern
    ( ReachabilityRule (..)
    )
import Kore.Step.Simplification.Simplify
import Kore.Step.Strategy
    ( ExecutionGraph (..)
    , GraphSearchOrder
    , Strategy
    , executionHistoryStep
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Step.Transition
    ( runTransitionT
    )
import Kore.Strategies.Goal
import Kore.Strategies.ProofState
    ( ProofStateTransformer (..)
    )
import qualified Kore.Strategies.ProofState as ProofState
import Kore.Syntax.Variable
import Kore.Unparser
import Logic
    ( LogicT
    )
import qualified Logic

type CommonProofState = ProofState.ProofState ReachabilityRule

-- | Extracts the left hand side (configuration) from the
-- 'CommonProofState'. If the 'ProofState' is 'Proven', then
-- the configuration will be '\\bottom'.
lhsProofStateTransformer
    :: ProofStateTransformer
        ReachabilityRule
        (Pattern VariableName)
lhsProofStateTransformer =
    ProofStateTransformer
        { goalTransformer = getConfiguration
        , goalRemainderTransformer = getConfiguration
        , goalRewrittenTransformer = getConfiguration
        , goalStuckTransformer = getConfiguration
        , provenValue = Pattern.bottom
        }

{- | @Verifer a@ is a 'Simplifier'-based action which returns an @a@.

The action may throw an exception if the proof fails; the exception is a single
@'Pattern' 'VariableName'@, the first unprovable configuration.

 -}
type Verifier m = ExceptT (OrPattern VariableName) m

{- | Verifies a set of claims. When it verifies a certain claim, after the
first step, it also uses the claims as axioms (i.e. it does coinductive proofs).

If the verification fails, returns an error containing a pattern that could
not be rewritten (either because no axiom could be applied or because we
didn't manage to verify a claim within the its maximum number of steps).

If the verification succeeds, it returns ().
-}
data Stuck =
    Stuck
    { stuckPatterns :: !(OrPattern VariableName)
    , provenClaims :: ![ReachabilityRule]
    }
    deriving (Eq, GHC.Generic, Show)

instance SOP.Generic Stuck

instance SOP.HasDatatypeInfo Stuck

instance Debug Stuck

instance Diff Stuck

newtype AllClaims claim = AllClaims {getAllClaims :: [claim]}
newtype Axioms claim = Axioms {getAxioms :: [Rule claim]}
newtype ToProve claim = ToProve {getToProve :: [(claim, Limit Natural)]}
newtype AlreadyProven = AlreadyProven {getAlreadyProven :: [Text]}

verify
    :: forall simplifier
    .  (MonadCatch simplifier, MonadSimplify simplifier)
    => Limit Natural
    -> GraphSearchOrder
    -> AllClaims ReachabilityRule
    -> Axioms ReachabilityRule
    -> AlreadyProven
    -> ToProve ReachabilityRule
    -- ^ List of claims, together with a maximum number of verification steps
    -- for each.
    -> ExceptT Stuck simplifier ()
verify
    breadthLimit
    searchOrder
    claims
    axioms
    (AlreadyProven alreadyProven)
    (ToProve toProve)
  =
    withExceptT addStillProven
    $ verifyHelper breadthLimit searchOrder claims axioms unproven
  where
    unproven :: ToProve ReachabilityRule
    stillProven :: [ReachabilityRule]
    (unproven, stillProven) =
        (ToProve newToProve, newAlreadyProven)
      where
        (newToProve, newAlreadyProven) =
            partitionEithers (map lookupEither toProve)
        lookupEither
            :: (ReachabilityRule, Limit Natural)
            -> Either (ReachabilityRule, Limit Natural) ReachabilityRule
        lookupEither claim@(rule, _) =
            if unparseToText2 rule `elem` alreadyProven
                then Right rule
                else Left claim

    addStillProven :: Stuck -> Stuck
    addStillProven stuck@Stuck { provenClaims } =
        stuck { provenClaims = stillProven ++ provenClaims }

verifyHelper
    :: forall simplifier
    .  (MonadCatch simplifier, MonadSimplify simplifier)
    => Limit Natural
    -> GraphSearchOrder
    -> AllClaims ReachabilityRule
    -> Axioms ReachabilityRule
    -> ToProve ReachabilityRule
    -- ^ List of claims, together with a maximum number of verification steps
    -- for each.
    -> ExceptT Stuck simplifier ()
verifyHelper breadthLimit searchOrder claims axioms (ToProve toProve) =
    Monad.foldM_ verifyWorker [] toProve
  where
    verifyWorker
        :: [ReachabilityRule]
        -> (ReachabilityRule, Limit Natural)
        -> ExceptT Stuck simplifier [ReachabilityRule]
    verifyWorker provenClaims unprovenClaim@(claim, _) =
        withExceptT wrapStuckPattern $ do
            verifyClaim breadthLimit searchOrder claims axioms unprovenClaim
            return (claim : provenClaims)
      where
        wrapStuckPattern :: OrPattern VariableName -> Stuck
        wrapStuckPattern stuckPatterns = Stuck { stuckPatterns, provenClaims }

verifyClaim
    :: forall simplifier
    .  (MonadCatch simplifier, MonadSimplify simplifier)
    => Limit Natural
    -> GraphSearchOrder
    -> AllClaims ReachabilityRule
    -> Axioms ReachabilityRule
    -> (ReachabilityRule, Limit Natural)
    -> ExceptT (OrPattern VariableName) simplifier ()
verifyClaim
    breadthLimit
    searchOrder
    (AllClaims claims)
    (Axioms axioms)
    (goal, depthLimit)
  =
    traceExceptT D_OnePath_verifyClaim [debugArg "rule" goal] $ do
    let
        startGoal = ProofState.Goal goal
        limitedStrategy =
            strategy goal claims axioms
            & Foldable.toList
            & Limit.takeWithin depthLimit
    handle
        handleLimitExceeded
        $ Strategy.leavesM
            updateQueue
            (Strategy.unfoldTransition transit)
            (limitedStrategy, startGoal)
            & fmap discardStrategy
            & throwUnproven
  where
    discardStrategy = snd

    handleLimitExceeded
        :: Strategy.LimitExceeded CommonProofState
        -> ExceptT (OrPattern VariableName) simplifier ()
    handleLimitExceeded (Strategy.LimitExceeded patterns) =
        Monad.Except.throwError
        . OrPattern.fromPatterns
        $ fmap
            (ProofState.proofState lhsProofStateTransformer)
            patterns

    updateQueue = \as ->
        Strategy.unfoldSearchOrder searchOrder as
        >=> lift . Strategy.applyBreadthLimit breadthLimit discardStrategy
        >=> profileQueueLength

    profileQueueLength queue = do
        Profile.executionQueueLength (length queue)
        pure queue

    throwUnproven
        :: LogicT (Verifier simplifier) CommonProofState
        -> Verifier simplifier ()
    throwUnproven acts =
        Logic.runLogicT acts throwUnprovenOrElse done
      where
        done = return ()

    throwUnprovenOrElse
        :: CommonProofState
        -> Verifier simplifier ()
        -> Verifier simplifier ()
    throwUnprovenOrElse proofState acts = do
        ProofState.extractUnproven proofState
            & Foldable.traverse_
                ( Monad.Except.throwError
                . OrPattern.fromPattern
                . getConfiguration
                )
        acts

    transit instr config =
        Strategy.transitionRule transitionRule instr config
        & runTransitionT
        & fmap (map fst)
        & lift

-- | Attempts to perform a single proof step, starting at the configuration
-- in the execution graph designated by the provided node. Re-constructs the
-- execution graph by inserting this step.
verifyClaimStep
    :: forall simplifier
    .  (MonadCatch simplifier, MonadSimplify simplifier)
    => ReachabilityRule
    -- ^ claim that is being proven
    -> [ReachabilityRule]
    -- ^ list of claims in the spec module
    -> [Rule ReachabilityRule]
    -- ^ list of axioms in the main module
    -> ExecutionGraph CommonProofState (Rule ReachabilityRule)
    -- ^ current execution graph
    -> Graph.Node
    -- ^ selected node in the graph
    -> simplifier (ExecutionGraph CommonProofState (Rule ReachabilityRule))
verifyClaimStep target claims axioms eg@ExecutionGraph { root } node =
    executionHistoryStep transitionRule strategy' eg node
  where
    strategy' :: Strategy (Prim ReachabilityRule)
    strategy'
        | isRoot = firstStep
        | otherwise = followupStep

    firstStep :: Strategy (Prim ReachabilityRule)
    firstStep = strategy target claims axioms Stream.!! 0

    followupStep :: Strategy (Prim ReachabilityRule)
    followupStep = strategy target claims axioms Stream.!! 1

    isRoot :: Bool
    isRoot = node == root
