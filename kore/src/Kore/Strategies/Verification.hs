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

import Control.DeepSeq
    ( deepseq
    )
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
import Kore.Log.DebugProven
import Kore.Log.InfoExecBreadth
import Kore.Log.InfoProofDepth
import Kore.Log.WarnTrivialClaim
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    , getRewritingPattern
    )
import Kore.Step.ClaimPattern
    ( lensClaimPattern
    , mkGoal
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

type CommonTransitionRule m =
    TransitionRule m (AppliedRule ReachabilityRule) CommonProofState

-- | Extracts the left hand side (configuration) from the
-- 'CommonProofState'. If the 'ProofState' is 'Proven', then
-- the configuration will be '\\bottom'.
lhsProofStateTransformer
    :: ProofStateTransformer
        ReachabilityRule
        (Pattern RewritingVariableName)
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
        startGoal = ProofState.Goal (Lens.over lensClaimPattern mkGoal goal)
        limitedStrategy =
            strategy
            & Foldable.toList
            & Limit.takeWithin depthLimit
    proofDepths <-
        Strategy.leavesM
            updateQueue
            (Strategy.unfoldTransition transit)
            (limitedStrategy, (ProofDepth 0, startGoal))
            & fmap discardStrategy
            & throwUnproven
            & handle handleLimitExceeded
    let maxProofDepth = sconcat (ProofDepth 0 :| proofDepths)
    infoProvenDepth maxProofDepth
    warnProvenClaimZeroDepth maxProofDepth goal
  where
    discardStrategy = snd

    handleLimitExceeded
        :: Strategy.LimitExceeded (ProofDepth, CommonProofState)
        -> Verifier simplifier a
    handleLimitExceeded (Strategy.LimitExceeded states) =
        let finalPattern =
                ProofState.proofState lhsProofStateTransformer
                . snd
                <$> states
         in
            Monad.Except.throwError
            . fmap getRewritingPattern
            . OrPattern.fromPatterns
            $ finalPattern

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
        :: LogicT (Verifier simplifier) (ProofDepth, CommonProofState)
        -> Verifier simplifier [ProofDepth]
    throwUnproven acts =
        do
            (proofDepth, proofState) <- acts
            let maybeUnproven = ProofState.extractUnproven proofState
            Foldable.for_ maybeUnproven $ \unproven -> do
                infoUnprovenDepth proofDepth
                Monad.Except.throwError . OrPattern.fromPattern
                    $ (getRewritingPattern . getConfiguration) unproven
            pure proofDepth
        & Logic.observeAllT

    discardAppliedRules = map fst

    transit instr config =
        Strategy.transitionRule
            (transitionRule' claims axioms & trackProofDepth)
            instr
            config
        & runTransitionT
        & fmap discardAppliedRules
        & traceProf ":transit"
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
    -> ExecutionGraph CommonProofState (AppliedRule ReachabilityRule)
    -- ^ current execution graph
    -> Graph.Node
    -- ^ selected node in the graph
    -> simplifier (ExecutionGraph CommonProofState (AppliedRule ReachabilityRule))
verifyClaimStep claims axioms executionGraph node =
    executionHistoryStep
        transitionRule''
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

    transitionRule'' prim state
        | isRoot =
            transitionRule'
                claims
                axioms
                prim
                (Lens.over lensClaimPattern mkGoal <$> state)
        | otherwise =
            transitionRule' claims axioms prim state

transitionRule'
    :: MonadSimplify simplifier
    => MonadProf simplifier
    => MonadMask simplifier
    => [ReachabilityRule]
    -> [Rule ReachabilityRule]
    -> CommonTransitionRule simplifier
transitionRule' claims axioms = \prim proofState ->
    deepseq proofState
    (transitionRule claims axiomGroups
        & profTransitionRule
        & withConfiguration
        & withDebugProofState
        & withDebugProven
        & logTransitionRule
    )
    prim proofState
  where
    axiomGroups = groupSortOn Attribute.Axiom.getPriorityOfAxiom axioms

profTransitionRule
    :: forall m
    .  MonadProf m
    => CommonTransitionRule m
    -> CommonTransitionRule m
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
    => CommonTransitionRule m
    -> CommonTransitionRule m
logTransitionRule rule prim proofState =
    whileReachability prim $ rule prim proofState

{- | Modify a 'TransitionRule' to track the depth of a proof.
 -}
trackProofDepth
    :: forall m rule goal
    .  TransitionRule m rule (ProofState goal)
    -> TransitionRule m rule (ProofDepth, ProofState goal)
trackProofDepth rule prim (!proofDepth, proofState) = do
    proofState' <- rule prim proofState
    let proofDepth' = (if didRewrite proofState' then succ else id) proofDepth
    pure (proofDepth', proofState')
  where
    didRewrite proofState' =
        isApply prim && isRewritable proofState && isRewritten proofState'

    isApply Prim.ApplyClaims = True
    isApply Prim.ApplyAxioms = True
    isApply _                = False

    isRewritable (ProofState.Goal _)          = True
    isRewritable (ProofState.GoalRemainder _) = True
    isRewritable _                            = False

    isRewritten (ProofState.GoalRewritten _) = True
    isRewritten  ProofState.Proven           = True
    isRewritten _                            = False

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
    => CommonTransitionRule monad
    -> CommonTransitionRule monad
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

withDebugProven
    :: forall monad
    .  MonadLog monad
    => CommonTransitionRule monad
    -> CommonTransitionRule monad
withDebugProven rule prim state =
    rule prim state >>= debugProven
  where
    debugProven state'
      | ProofState.Proven <- state'
      , Just claim <- ProofState.extractUnproven state
      = do
        Log.logEntry DebugProven { claim }
        pure state'
      | otherwise = pure state'

withConfiguration
    :: MonadCatch monad
    => CommonTransitionRule monad
    -> CommonTransitionRule monad
withConfiguration transit prim proofState =
    handle' (transit prim proofState)
  where
    config =
        ProofState.extractUnproven proofState
        & fmap getConfiguration
    handle' =
        maybe id handleConfig config
    handleConfig config' =
        handleAll
        $ throwM
        . WithConfiguration (getRewritingPattern config')
