{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com

This should be imported qualified.
-}
module Kore.Reachability.Prove (
    CommonClaimState,
    ProveClaimsResult (..),
    StuckClaim (..),
    StuckClaims,
    AllClaims (..),
    Axioms (..),
    ToProve (..),
    AlreadyProven (..),
    proveClaims,
    proveClaimStep,
    lhsClaimStateTransformer,
) where

import Control.DeepSeq (
    deepseq,
 )
import qualified Control.Lens as Lens
import Control.Monad (
    (>=>),
 )
import Control.Monad.Catch (
    MonadCatch,
    MonadMask,
    handle,
    handleAll,
    throwM,
 )
import Control.Monad.Except (
    ExceptT,
    runExceptT,
 )
import qualified Control.Monad.Except as Monad.Except
import Control.Monad.State.Strict (
    StateT,
    evalStateT,
    runStateT,
 )
import qualified Control.Monad.State.Strict as State
import qualified Data.Graph.Inductive.Graph as Graph
import Data.Limit (
    Limit,
 )
import qualified Data.Limit as Limit
import Data.List.Extra (
    groupSortOn,
 )
import Data.Text (
    Text,
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import qualified Kore.Attribute.Axiom as Attribute.Axiom
import Kore.Debug
import Kore.Internal.Conditional (
    Conditional (..),
 )
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    Predicate,
    getMultiAndPredicate,
    pattern PredicateCeil,
    pattern PredicateNot,
 )
import Kore.Log.DebugBeginClaim
import Kore.Log.DebugProven
import Kore.Log.DebugTransition (
    debugAfterTransition,
    debugBeforeTransition,
    debugFinalTransition,
 )
import Kore.Log.InfoExecBreadth
import Kore.Log.InfoProofDepth
import Kore.Log.WarnStuckClaimState
import Kore.Log.WarnTrivialClaim
import Kore.Reachability.Claim
import Kore.Reachability.ClaimState (
    ClaimState,
    ClaimStateTransformer (..),
    extractStuck,
    extractUnproven,
 )
import qualified Kore.Reachability.ClaimState as ClaimState
import qualified Kore.Reachability.Prim as Prim (
    Prim (..),
 )
import Kore.Reachability.SomeClaim
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
    getRewritingPattern,
 )
import Kore.Step.ClaimPattern (
    mkGoal,
 )
import Kore.Step.Simplification.Simplify
import Kore.Step.Strategy (
    ExecutionGraph (..),
    GraphSearchOrder,
    Strategy,
    executionHistoryStep,
 )
import qualified Kore.Step.Strategy as Strategy
import Kore.Step.Transition (
    runTransitionT,
 )
import qualified Kore.Step.Transition as Transition
import Kore.TopBottom
import Kore.Unparser
import Log (
    MonadLog (..),
 )
import Logic (
    LogicT,
 )
import qualified Logic
import Numeric.Natural (
    Natural,
 )
import Prelude.Kore
import qualified Pretty
import Prof

type CommonClaimState = ClaimState.ClaimState SomeClaim

type CommonTransitionRule m =
    TransitionRule m (AppliedRule SomeClaim) CommonClaimState

{- | Extracts the left hand side (configuration) from the
 'CommonClaimState'. If the 'ClaimState' is 'Proven', then
 the configuration will be '\\bottom'.
-}
lhsClaimStateTransformer ::
    ClaimStateTransformer
        SomeClaim
        (Pattern RewritingVariableName)
lhsClaimStateTransformer =
    ClaimStateTransformer
        { claimedTransformer = getConfiguration
        , remainingTransformer = getConfiguration
        , rewrittenTransformer = getConfiguration
        , stuckTransformer = getConfiguration
        , provenValue = Pattern.bottom
        }

{- | @Verifer a@ is a 'Simplifier'-based action which returns an @a@.

The action may throw an exception if the proof fails; the exception is a single
@'Pattern' 'VariableName'@, the first unprovable configuration.
-}
type VerifierT m = StateT StuckClaims (ExceptT StuckClaims m)

newtype AllClaims claim = AllClaims {getAllClaims :: [claim]}
newtype Axioms claim = Axioms {getAxioms :: [Rule claim]}
newtype ToProve claim = ToProve {getToProve :: [(claim, Limit Natural)]}
newtype AlreadyProven = AlreadyProven {getAlreadyProven :: [Text]}

newtype StuckClaim = StuckClaim {getStuckClaim :: SomeClaim}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance TopBottom StuckClaim where
    isTop = const False
    isBottom = const False

type StuckClaims = MultiAnd StuckClaim

type ProvenClaims = MultiAnd SomeClaim

-- | The result of proving some claims.
data ProveClaimsResult = ProveClaimsResult
    { -- | The conjuction of stuck claims, that is: of claims which must still be
      -- proven. If all claims were proved, then the remaining claims are @\\top@.
      stuckClaims :: !StuckClaims
    , -- | The conjunction of all claims which were proven.
      provenClaims :: !ProvenClaims
    }

proveClaims ::
    forall simplifier.
    MonadMask simplifier =>
    MonadSimplify simplifier =>
    MonadProf simplifier =>
    Limit Natural ->
    GraphSearchOrder ->
    Natural ->
    AllClaims SomeClaim ->
    Axioms SomeClaim ->
    AlreadyProven ->
    -- | List of claims, together with a maximum number of verification steps
    -- for each.
    ToProve SomeClaim ->
    simplifier ProveClaimsResult
proveClaims
    breadthLimit
    searchOrder
    maxCounterexamples
    claims
    axioms
    (AlreadyProven alreadyProven)
    (ToProve toProve) =
        do
            (result, provenClaims) <-
                proveClaimsWorker
                    breadthLimit
                    searchOrder
                    maxCounterexamples
                    claims
                    axioms
                    unproven
                    & runExceptT
                    & flip runStateT (MultiAnd.make stillProven)
            pure
                ProveClaimsResult
                    { stuckClaims = fromLeft MultiAnd.top result
                    , provenClaims
                    }
      where
        unproven :: ToProve SomeClaim
        stillProven :: [SomeClaim]
        (unproven, stillProven) =
            (ToProve newToProve, newAlreadyProven)
          where
            (newToProve, newAlreadyProven) =
                partitionEithers (map lookupEither toProve)
            lookupEither ::
                (SomeClaim, Limit Natural) ->
                Either (SomeClaim, Limit Natural) SomeClaim
            lookupEither claim@(rule, _) =
                if unparseToText2 rule `elem` alreadyProven
                    then Right rule
                    else Left claim

proveClaimsWorker ::
    forall simplifier.
    MonadSimplify simplifier =>
    MonadMask simplifier =>
    MonadProf simplifier =>
    Limit Natural ->
    GraphSearchOrder ->
    Natural ->
    AllClaims SomeClaim ->
    Axioms SomeClaim ->
    -- | List of claims, together with a maximum number of verification steps
    -- for each.
    ToProve SomeClaim ->
    ExceptT StuckClaims (StateT ProvenClaims simplifier) ()
proveClaimsWorker
    breadthLimit
    searchOrder
    maxCounterexamples
    claims
    axioms
    (ToProve toProve) =
        traverse_ verifyWorker toProve
      where
        verifyWorker ::
            (SomeClaim, Limit Natural) ->
            ExceptT StuckClaims (StateT ProvenClaims simplifier) ()
        verifyWorker unprovenClaim@(claim, _) = do
            debugBeginClaim claim
            proveClaim
                breadthLimit
                searchOrder
                maxCounterexamples
                claims
                axioms
                unprovenClaim
            addProvenClaim claim

        addProvenClaim claim =
            State.modify' (mappend (MultiAnd.singleton claim))

proveClaim ::
    forall simplifier.
    MonadSimplify simplifier =>
    MonadMask simplifier =>
    MonadProf simplifier =>
    Limit Natural ->
    GraphSearchOrder ->
    Natural ->
    AllClaims SomeClaim ->
    Axioms SomeClaim ->
    (SomeClaim, Limit Natural) ->
    ExceptT StuckClaims simplifier ()
proveClaim
    breadthLimit
    searchOrder
    maxCounterexamples
    (AllClaims claims)
    (Axioms axioms)
    (goal, depthLimit) =
        traceExceptT D_OnePath_verifyClaim [debugArg "rule" goal] $ do
            let startGoal = ClaimState.Claimed (Lens.over lensClaimPattern mkGoal goal)
                limitedStrategy =
                    strategy
                        & toList
                        & Limit.takeWithin depthLimit
            proofDepths <-
                Strategy.leavesM
                    updateQueue
                    (Strategy.unfoldTransition transit)
                    (limitedStrategy, (ProofDepth 0, startGoal))
                    & fmap discardStrategy
                    & throwUnproven
                    & handle handleLimitExceeded
                    & (\s -> evalStateT s mempty)
            let maxProofDepth = sconcat (ProofDepth 0 :| proofDepths)
            infoProvenDepth maxProofDepth
            warnProvenClaimZeroDepth maxProofDepth goal
      where
        discardStrategy = snd

        handleLimitExceeded ::
            Strategy.LimitExceeded (ProofDepth, CommonClaimState) ->
            VerifierT simplifier a
        handleLimitExceeded (Strategy.LimitExceeded states) = do
            let extractStuckClaim = fmap StuckClaim . extractUnproven . snd
                stuckClaims = mapMaybe extractStuckClaim states
            Monad.Except.throwError (MultiAnd.make $ toList stuckClaims)

        updateQueue = \as ->
            Strategy.unfoldSearchOrder searchOrder as
                >=> lift . Strategy.applyBreadthLimit breadthLimit discardStrategy
                >=> ( \queue ->
                        infoExecBreadth (ExecBreadth $ genericLength queue)
                            >> return queue
                    )
          where
            genericLength = fromIntegral . length

        throwUnproven ::
            LogicT (VerifierT simplifier) (ProofDepth, CommonClaimState) ->
            VerifierT simplifier [ProofDepth]
        throwUnproven acts =
            do
                (proofDepth, proofState) <- acts
                let maybeUnproven = extractUnproven proofState
                for_ maybeUnproven $ \unproven -> lift $ do
                    infoUnprovenDepth proofDepth
                    updateSuckClaimsState unproven maxCounterexamples
                pure proofDepth
                & Logic.observeAllT
                >>= checkLeftUnproven

        checkLeftUnproven ::
            [ProofDepth] ->
            VerifierT simplifier [ProofDepth]
        checkLeftUnproven depths =
            do
                stuck <- State.get
                if (null stuck)
                    then pure depths
                    else Monad.Except.throwError stuck

        discardAppliedRules = map fst

        transit instr config =
            Strategy.transitionRule
                ( transitionRule' claims axioms
                    & trackProofDepth
                    & throwStuckClaims maxCounterexamples
                )
                instr
                config
                & runTransitionT
                & fmap discardAppliedRules
                & traceProf ":transit"
                & lift

{- | Attempts to perform a single proof step, starting at the configuration
 in the execution graph designated by the provided node. Re-constructs the
 execution graph by inserting this step.
-}
proveClaimStep ::
    forall simplifier.
    MonadSimplify simplifier =>
    MonadMask simplifier =>
    MonadProf simplifier =>
    -- | list of claims in the spec module
    [SomeClaim] ->
    -- | list of axioms in the main module
    [Rule SomeClaim] ->
    -- | current execution graph
    ExecutionGraph CommonClaimState (AppliedRule SomeClaim) ->
    -- | selected node in the graph
    Graph.Node ->
    simplifier (ExecutionGraph CommonClaimState (AppliedRule SomeClaim))
proveClaimStep claims axioms executionGraph node =
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

    ExecutionGraph{root} = executionGraph

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

transitionRule' ::
    MonadSimplify simplifier =>
    MonadProf simplifier =>
    MonadMask simplifier =>
    [SomeClaim] ->
    [Rule SomeClaim] ->
    CommonTransitionRule simplifier
transitionRule' claims axioms = \prim proofState ->
    deepseq
        proofState
        ( transitionRule claims axiomGroups
            & withWarnings
            & profTransitionRule
            & withConfiguration
            & withDebugClaimState
            & withDebugProven
            & logTransitionRule
            & checkStuckConfiguration
        )
        prim
        proofState
  where
    axiomGroups = groupSortOn Attribute.Axiom.getPriorityOfAxiom axioms

withWarnings ::
    forall m.
    MonadSimplify m =>
    CommonTransitionRule m ->
    CommonTransitionRule m
withWarnings rule prim claimState = do
    claimState' <- rule prim claimState
    case prim of
        Prim.CheckImplication | ClaimState.Stuck _ <- claimState' ->
            case claimState of
                ClaimState.Remaining claim -> warnStuckClaimStateTermsNotUnifiable claim
                ClaimState.Claimed claim -> warnStuckClaimStateTermsUnifiable claim
                _ -> return ()
        _ -> return ()
    return claimState'

profTransitionRule ::
    forall m.
    MonadProf m =>
    CommonTransitionRule m ->
    CommonTransitionRule m
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

logTransitionRule ::
    forall m.
    MonadSimplify m =>
    CommonTransitionRule m ->
    CommonTransitionRule m
logTransitionRule rule prim proofState =
    whileReachability prim $ rule prim proofState

checkStuckConfiguration ::
    CommonTransitionRule m ->
    CommonTransitionRule m
checkStuckConfiguration rule prim proofState = do
    proofState' <- rule prim proofState
    for_ (extractStuck proofState) $ \rule' -> do
        let resultPatternPredicate = predicate (getConfiguration rule')
            multiAndPredicate = getMultiAndPredicate resultPatternPredicate
        when (any isNot_Ceil_ multiAndPredicate) $
            error . show . Pretty.vsep $
                [ "Found '\\not(\\ceil(_))' in stuck configuration:"
                , Pretty.pretty rule'
                , "Please file a bug report:\
                  \ https://github.com/kframework/kore/issues"
                ]
    return proofState'
  where
    isNot_Ceil_ :: Predicate variable -> Bool
    isNot_Ceil_ (PredicateNot (PredicateCeil _)) = True
    isNot_Ceil_ _ = False

-- | Terminate the prover after 'maxCounterexamples' stuck steps.
throwStuckClaims ::
    forall m rule.
    MonadLog m =>
    Natural ->
    TransitionRule
        (VerifierT m)
        rule
        (ProofDepth, ClaimState SomeClaim) ->
    TransitionRule
        (VerifierT m)
        rule
        (ProofDepth, ClaimState SomeClaim)
throwStuckClaims maxCounterexamples rule prim state = do
    state'@(proofDepth', proofState') <- rule prim state
    case proofState' of
        ClaimState.Stuck unproven -> do
            lift $ do
                infoUnprovenDepth proofDepth'
                updateSuckClaimsState unproven maxCounterexamples
                return state'
        _ -> return state'

updateSuckClaimsState ::
    Monad m =>
    SomeClaim ->
    Natural ->
    VerifierT m ()
updateSuckClaimsState unproven maxCounterexamples = do
    stuckClaims <- State.get
    let updatedStuck =
            MultiAnd.singleton (StuckClaim unproven) <> stuckClaims
    when (MultiAnd.size updatedStuck >= maxCounterexamples) $ do
        Monad.Except.throwError updatedStuck
    State.put updatedStuck

-- | Modify a 'TransitionRule' to track the depth of a proof.
trackProofDepth ::
    forall m rule goal.
    TransitionRule m rule (ClaimState goal) ->
    TransitionRule m rule (ProofDepth, ClaimState goal)
trackProofDepth rule prim (!proofDepth, proofState) = do
    proofState' <- rule prim proofState
    let proofDepth' = (if didRewrite proofState' then succ else id) proofDepth
    pure (proofDepth', proofState')
  where
    didRewrite proofState' =
        isApply prim
            && ClaimState.isRewritable proofState
            && isRewritten proofState'

    isApply Prim.ApplyClaims = True
    isApply Prim.ApplyAxioms = True
    isApply _ = False

    isRewritten (ClaimState.Rewritten _) = True
    isRewritten ClaimState.Proven = True
    isRewritten _ = False

debugClaimStateBracket ::
    forall monad rule.
    MonadLog monad =>
    From rule Attribute.Axiom.SourceLocation =>
    -- | current proof state
    ClaimState SomeClaim ->
    -- | transition
    Prim ->
    -- | action to be computed
    Transition.TransitionT rule monad (ClaimState SomeClaim) ->
    Transition.TransitionT rule monad (ClaimState SomeClaim)
debugClaimStateBracket proofState transition action = do
    debugBeforeTransition proofState transition
    (result, rules) <- Transition.record action
    debugAfterTransition result transition $ toList rules
    return result

debugClaimStateFinal ::
    forall monad.
    Alternative monad =>
    MonadLog monad =>
    -- | transition
    Prim ->
    monad (ClaimState SomeClaim)
debugClaimStateFinal transition = do
    debugFinalTransition transition
    empty

withDebugClaimState ::
    forall monad.
    MonadLog monad =>
    CommonTransitionRule monad ->
    CommonTransitionRule monad
withDebugClaimState transitionFunc transition state =
    Transition.orElse
        ( debugClaimStateBracket
            state
            transition
            (transitionFunc transition state)
        )
        ( debugClaimStateFinal
            transition
        )

withDebugProven ::
    forall monad.
    MonadLog monad =>
    CommonTransitionRule monad ->
    CommonTransitionRule monad
withDebugProven rule prim state =
    do
        state' <- rule prim state
        case state' of
            ClaimState.Proven ->
                case extractUnproven state of
                    Just claim ->
                        do
                            Log.logEntry DebugProven{claim}
                            pure state'
                    _ -> pure state'
            _ -> pure state'

withConfiguration ::
    MonadCatch monad =>
    CommonTransitionRule monad ->
    CommonTransitionRule monad
withConfiguration transit prim proofState =
    handle' (transit prim proofState)
  where
    config = extractUnproven proofState & fmap getConfiguration
    handle' = maybe id handleConfig config
    handleConfig config' =
        handleAll $
            throwM
                . WithConfiguration (getRewritingPattern config')
