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
    , depthAndLhsProofStateTransformer
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Control.Monad
    ( (>=>)
    )
import qualified Control.Monad as Monad
    ( foldM_
    )
import Control.Monad.Catch
    ( MonadCatch
    , handle
    , handleAll
    , throwM
    )
import Control.Monad.Except
    ( ExceptT
    , catchError
    , throwError
    , withExceptT
    )
import qualified Control.Monad.Except as Monad.Except
import qualified Data.Bifunctor as Bifunctor
import Data.Coerce
    ( coerce
    )
import qualified Data.Foldable as Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import Data.List.Extra
    ( groupSortOn
    )
import qualified Data.Sequence as Seq
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
import qualified Kore.Attribute.Axiom as Attribute.Axiom
import Kore.Debug
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Log.DebugProofState
import Kore.Log.InfoExecutionDepth
    ( infoUnprovenDepth
    )
import qualified Kore.Profiler.Profile as Profile
import Kore.Step.RulePattern
    ( ReachabilityRule (..)
    , leftPattern
    , toRulePattern
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
import qualified Kore.Step.Transition as Transition
import Kore.Strategies.Goal
import Kore.Strategies.ProofState
    ( ExecutionDepth (..)
    , ProofState
    , ProofStateTransformer (..)
    , incrementDepth
    )
import qualified Kore.Strategies.ProofState as ProofState
    ( ProofState (..)
    , extractDepth
    , extractUnproven
    , proofState
    )
import qualified Kore.Strategies.ProofState as Prim
    ( Prim (..)
    )
import Kore.Syntax.Variable
import Kore.Unparser
import Log
    ( MonadLog (..)
    )
import Logic
    ( LogicT
    )
import qualified Logic

type CommonProofState = ProofState.ProofState ReachabilityRule

-- | Extracts the left hand side (configuration) from the
-- 'CommonProofState'. If the 'ProofState' is 'Proven', then
-- the configuration will be '\\bottom'.
depthAndLhsProofStateTransformer
    :: ProofStateTransformer
        ReachabilityRule
        (ExecutionDepth, Pattern VariableName)
depthAndLhsProofStateTransformer =
    ProofStateTransformer
        { goalTransformer =
            \depth goal -> (depth, getConfiguration goal)
        , goalRemainderTransformer =
            \depth goal -> (depth, getConfiguration goal)
        , goalRewrittenTransformer =
            \depth goal -> (depth, getConfiguration goal)
        , goalStuckTransformer =
            \depth goal -> (depth, getConfiguration goal)
        , provenValue =
            \depth -> (depth, Pattern.bottom)
        }

{- | @Verifer a@ is a 'Simplifier'-based action which returns an @a@.

The action may throw an exception if the proof fails; the exception is a single
@'Pattern' 'VariableName'@, the first unprovable configuration.

 -}
type Verifier m = ExceptT (ExecutionDepth, OrPattern VariableName) m

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
            let verified =
                    verifyClaim
                        breadthLimit
                        searchOrder
                        claims
                        axioms
                        unprovenClaim
            catchError verified logExceptionHandler
            return (claim : provenClaims)
      where
        wrapStuckPattern
            :: (ExecutionDepth, OrPattern VariableName) -> Stuck
        wrapStuckPattern (_ ,stuckPatterns) =
            Stuck { stuckPatterns, provenClaims }

        logExceptionHandler e@(depth, _) = do
            infoUnprovenDepth depth
            throwError e

verifyClaim
    :: forall simplifier
    .  (MonadCatch simplifier, MonadSimplify simplifier)
    => Limit Natural
    -> GraphSearchOrder
    -> AllClaims ReachabilityRule
    -> Axioms ReachabilityRule
    -> (ReachabilityRule, Limit Natural)
    -> ExceptT (ExecutionDepth, OrPattern VariableName) simplifier ()
verifyClaim
    breadthLimit
    searchOrder
    (AllClaims claims)
    (Axioms axioms)
    (goal, depthLimit)
  =
    traceExceptT D_OnePath_verifyClaim [debugArg "rule" goal] $ do
    let
        startGoal = ProofState.Goal (ExecutionDepth 0) goal
        limitedStrategy =
            strategy
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
        -> ExceptT (ExecutionDepth, OrPattern VariableName) simplifier ()
    handleLimitExceeded (Strategy.LimitExceeded patterns) =
        Monad.Except.throwError
        $ Bifunctor.bimap headOrZero OrPattern.fromPatterns
        $ Seq.unzip
        $ fmap
            (ProofState.proofState depthAndLhsProofStateTransformer)
            patterns
      where
        headOrZero
            :: Seq.Seq ExecutionDepth
            -> ExecutionDepth
        headOrZero depths =
            fromMaybe (ExecutionDepth 0) $ Seq.lookup 0 depths

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
                . (,) (ProofState.extractDepth proofState)
                . OrPattern.fromPattern
                . getConfiguration
                )
        acts

    transit instr config =
        Strategy.transitionRule (transitionRule' claims axioms) instr config
        & runTransitionT
        & fmap (map fst)
        & lift

-- | Attempts to perform a single proof step, starting at the configuration
-- in the execution graph designated by the provided node. Re-constructs the
-- execution graph by inserting this step.
verifyClaimStep
    :: forall simplifier
    .  (MonadCatch simplifier, MonadSimplify simplifier)
    => [ReachabilityRule]
    -- ^ list of claims in the spec module
    -> [Rule ReachabilityRule]
    -- ^ list of axioms in the main module
    -> ExecutionGraph CommonProofState (Rule ReachabilityRule)
    -- ^ current execution graph
    -> Graph.Node
    -- ^ selected node in the graph
    -> simplifier (ExecutionGraph CommonProofState (Rule ReachabilityRule))
verifyClaimStep claims axioms executionGraph node =
    executionHistoryStep
        (transitionRule' claims axioms)
        strategy'
        executionGraph
        node
  where
    strategy' :: Strategy Prim
    strategy'
        | isRoot = firstStep
        | otherwise = followupStep

    firstStep :: Strategy Prim
    firstStep = reachabilityFirstStep

    followupStep :: Strategy Prim
    followupStep = reachabilityNextStep

    ExecutionGraph { root } = executionGraph

    isRoot :: Bool
    isRoot = node == root

transitionRule'
    :: MonadSimplify simplifier
    => MonadCatch simplifier
    => [ReachabilityRule]
    -> [Rule ReachabilityRule]
    -> TransitionRule simplifier ReachabilityRule
transitionRule' claims axioms =
    transitionRule claims axiomGroups
    & withConfiguration
    & withDebugProofState
    & logTransitionRule
    & countExecutionDepth
  where
    axiomGroups = groupSortOn Attribute.Axiom.getPriorityOfAxiom axioms

countExecutionDepth
    :: TransitionRule m ReachabilityRule
    -> TransitionRule m ReachabilityRule
countExecutionDepth rule = \prim proofState -> do
    traceM $ "countExecutionDepth " <> show (ProofState.extractDepth proofState)
    result <- rule prim proofState
    if prim `elem` [Prim.ApplyClaims, Prim.ApplyAxioms]
        && isGoalRemainder result
    then do
        traceM $ "To Increment Depth "
            <> show (ProofState.extractDepth (incrementDepth proofState))
        fmap incrementDepth (rule prim proofState)
    else
        rule prim proofState
  where
    isGoalRemainder (ProofState.GoalRemainder _ _) = True
    isGoalRemainder _ = False

logTransitionRule
    :: forall m
    .  MonadSimplify m
    => TransitionRule m ReachabilityRule
    -> TransitionRule m ReachabilityRule
logTransitionRule rule prim proofState =
    case proofState of
        ProofState.Goal _ goal          -> logWith goal
        ProofState.GoalRemainder _ goal -> logWith goal
        _                               -> rule prim proofState
  where
    logWith goal = case prim of
        Prim.Simplify ->
            whileSimplify goal $ rule prim proofState
        Prim.CheckImplication ->
            whileCheckImplication goal $ rule prim proofState
        _ ->
            rule prim proofState

debugProofStateBracket
    :: forall monad
    .  MonadLog monad
    => ProofState ReachabilityRule
    -- ^ current proof state
    -> Prim
    -- ^ transition
    -> monad (ProofState ReachabilityRule)
    -- ^ action to be computed
    -> monad (ProofState ReachabilityRule)
debugProofStateBracket
    proofState
    (coerce -> transition)
    action
  = do
    result <- action
    logEntry DebugProofState
        { proofState
        , transition
        , result = Just result
        }
    return result

debugProofStateFinal
    :: forall monad
    .  Alternative monad
    => MonadLog monad
    => ProofState ReachabilityRule
    -- ^ current proof state
    -> Prim
    -- ^ transition
    -> monad (ProofState ReachabilityRule)
debugProofStateFinal proofState (coerce -> transition) = do
    logEntry DebugProofState
        { proofState
        , transition
        , result = Nothing
        }
    empty

withDebugProofState
    :: forall monad
    .  MonadLog monad
    => TransitionRule monad ReachabilityRule
    -> TransitionRule monad ReachabilityRule
withDebugProofState transitionFunc =
    \transition state ->
        Transition.orElse
            (debugProofStateBracket
                state
                transition
                (transitionFunc transition state)
            )
            (debugProofStateFinal
                state
                transition
            )

withConfiguration
    :: MonadCatch monad
    => TransitionRule monad ReachabilityRule
    -> TransitionRule monad ReachabilityRule
withConfiguration transit prim proofState =
    handle' (transit prim proofState)
  where
    config =
        ProofState.extractUnproven proofState
        & fmap (Lens.view leftPattern . toRulePattern)
    handle' = maybe id (\c -> handleAll (throwM . WithConfiguration c)) config
