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

import qualified Control.Lens as Lens
import Control.Monad
    ( (>=>)
    )
import qualified Control.Monad as Monad
    ( foldM_
    )
import Control.Monad.Catch
    ( MonadCatch
    , MonadMask
    , handle
    , handleAll
    , throwM
    )
import Control.Monad.Except
    ( ExceptT
    , withExceptT
    )
import qualified Control.Monad.Except as Monad.Except
import Data.Coerce
    ( coerce
    )
import qualified Data.Foldable as Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import Data.List.Extra
    ( groupSortOn
    )
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
import Kore.Log.InfoExecBreadth
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
    ( ProofState
    , ProofStateTransformer (..)
    )
import qualified Kore.Strategies.ProofState as ProofState
    ( ProofState (..)
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
import Prof

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
    .  MonadMask simplifier
    => MonadSimplify simplifier
    => MonadProf simplifier
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
    .  MonadSimplify simplifier
    => MonadMask simplifier
    => MonadProf simplifier
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
    .  MonadSimplify simplifier
    => MonadMask simplifier
    => MonadProf simplifier
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
        >=> ( \queue ->
                infoExecBreadth (ExecBreadth $ genericLength queue)
                >> return queue
            )
      where
        genericLength = fromIntegral . length

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
        Strategy.transitionRule (transitionRule' claims axioms) instr config
        & runTransitionT
        & fmap (map fst)
        & lift

-- | Attempts to perform a single proof step, starting at the configuration
-- in the execution graph designated by the provided node. Re-constructs the
-- execution graph by inserting this step.
verifyClaimStep
    :: forall simplifier
    .  MonadSimplify simplifier
    => MonadMask simplifier
    => MonadProf simplifier
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
    => MonadProf simplifier
    => MonadMask simplifier
    => [ReachabilityRule]
    -> [Rule ReachabilityRule]
    -> TransitionRule simplifier ReachabilityRule
transitionRule' claims axioms =
    transitionRule claims axiomGroups
    & profTransitionRule
    & withConfiguration
    & withDebugProofState
    & logTransitionRule
  where
    axiomGroups = groupSortOn Attribute.Axiom.getPriorityOfAxiom axioms

profTransitionRule
    :: forall m
    .  MonadProf m
    => TransitionRule m ReachabilityRule
    -> TransitionRule m ReachabilityRule
profTransitionRule rule prim proofState =
    case prim of
        Prim.ApplyClaims -> tracing ":transit:apply-claims"
        Prim.ApplyAxioms -> tracing ":transit:apply-axioms"
        Prim.CheckImplication -> tracing ":transit:check-implies"
        Prim.Simplify -> tracing ":transit:simplify"
        _ -> rule prim proofState
  where
    tracing name =
        lift (traceProf name (runTransitionT (rule prim proofState)))
        >>= Transition.scatter

logTransitionRule
    :: forall m
    .  MonadSimplify m
    => TransitionRule m ReachabilityRule
    -> TransitionRule m ReachabilityRule
logTransitionRule rule prim proofState =
    case proofState of
        ProofState.Goal goal          -> logWith goal
        ProofState.GoalRemainder goal -> logWith goal
        _                  -> rule prim proofState
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
