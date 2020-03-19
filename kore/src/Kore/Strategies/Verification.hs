{-|
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com

This should be imported qualified.
-}

module Kore.Strategies.Verification
    ( Claim
    , CommonProofState
    , StuckVerification (..)
    , AllClaims (..)
    , Axioms (..)
    , ToProve (..)
    , AlreadyProven (..)
    , verify
    , verifyClaimStep
    , toRulePattern
    , commonProofStateTransformer
    ) where

import Prelude.Kore

import Control.Error
    ( partitionEithers
    )
import qualified Control.Monad as Monad
    ( foldM_
    )
import Control.Monad.Catch
    ( MonadCatch
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
import Data.Typeable
    ( Typeable
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
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Step.Rule.Expand
import Kore.Step.Rule.Simplify
import Kore.Step.RulePattern
    ( RHS
    )
import Kore.Step.Simplification.Simplify
import Kore.Step.Strategy
import Kore.Step.Transition
    ( runTransitionT
    )
import qualified Kore.Step.Transition as Transition
import Kore.Strategies.Goal
import Kore.Strategies.ProofState
    ( ProofStateTransformer (..)
    )
import qualified Kore.Strategies.ProofState as ProofState
import Kore.Syntax.Variable
    ( Variable
    )
import Kore.Unparser

type CommonProofState  = ProofState.ProofState (Pattern Variable)

commonProofStateTransformer :: ProofStateTransformer (Pattern Variable) (Pattern Variable)
commonProofStateTransformer =
    ProofStateTransformer
        { goalTransformer = id
        , goalRemainderTransformer = id
        , goalRewrittenTransformer = id
        , goalStuckTransformer = id
        , provenValue = Pattern.bottom
        }

{- | Class type for claim-like rules
-}
type Claim claim =
    ( ToRulePattern claim
    , ToRulePattern (Rule claim)
    , FromRulePattern claim
    , FromRulePattern (Rule claim)
    , Unparse claim
    , Unparse (Rule claim)
    , Goal claim
    , ClaimExtractor claim
    , ExpandSingleConstructors claim
    , SimplifyRuleLHS claim
    , Typeable claim
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

data StuckVerification patt claim
    = StuckVerification
        { stuckDescription :: !patt
        , provenClaims :: ![claim]
        }
    deriving (Eq, GHC.Generic, Show)

instance SOP.Generic (StuckVerification patt claim)

instance SOP.HasDatatypeInfo (StuckVerification patt claim)

instance (Debug patt, Debug claim) => Debug (StuckVerification patt claim)

instance (Debug patt, Debug claim, Diff patt, Diff claim)
    => Diff (StuckVerification patt claim)

newtype AllClaims claim = AllClaims {getAllClaims :: [claim]}
newtype Axioms claim = Axioms {getAxioms :: [Rule claim]}
newtype ToProve claim = ToProve {getToProve :: [(claim, Limit Natural)]}
newtype AlreadyProven = AlreadyProven {getAlreadyProven :: [Text]}

verify
    :: forall claim m
    .  Claim claim
    => ProofState claim (Pattern Variable) ~ CommonProofState
    => Show claim
    => (MonadCatch m, MonadSimplify m)
    => Show (Rule claim)
    => Limit Natural
    -> GraphSearchOrder
    -> AllClaims claim
    -> Axioms claim
    -> AlreadyProven
    -> ToProve claim
    -- ^ List of claims, together with a maximum number of verification steps
    -- for each.
    -> ExceptT (StuckVerification (Pattern Variable) claim) m ()
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
    unproven :: ToProve claim
    stillProven :: [claim]
    (unproven, stillProven) =
        (ToProve newToProve, newAlreadyProven)
      where
        (newToProve, newAlreadyProven) =
            partitionEithers (map lookupEither toProve)
        lookupEither
            :: (claim, Limit Natural)
            -> Either (claim, Limit Natural) claim
        lookupEither claim@(rule, _) =
            if unparseToText2 rule `elem` alreadyProven
                then Right rule
                else Left claim

    addStillProven
        :: StuckVerification (Pattern Variable) claim
        -> StuckVerification (Pattern Variable) claim
    addStillProven
        StuckVerification { stuckDescription, provenClaims }
      =
        StuckVerification
            { stuckDescription, provenClaims = stillProven ++ provenClaims }

verifyHelper
    :: forall claim m
    .  Claim claim
    => ProofState claim (Pattern Variable) ~ CommonProofState
    => Show claim
    => (MonadCatch m, MonadSimplify m)
    => Show (Rule claim)
    => Limit Natural
    -> GraphSearchOrder
    -> AllClaims claim
    -> Axioms claim
    -> ToProve claim
    -- ^ List of claims, together with a maximum number of verification steps
    -- for each.
    -> ExceptT (StuckVerification (Pattern Variable) claim) m ()
verifyHelper
    breadthLimit
    searchOrder
    claims
    axioms
    (ToProve toProve)
  =
    Monad.foldM_ verifyWorker [] toProve
  where
    verifyWorker
        :: [claim]
        -> (claim, Limit Natural)
        -> ExceptT (StuckVerification (Pattern Variable) claim) m [claim]
    verifyWorker provenClaims unprovenClaim@(claim, _) =
        withExceptT wrapStuckPattern $ do
            verifyClaim breadthLimit searchOrder claims axioms unprovenClaim
            return (claim : provenClaims)
      where
        wrapStuckPattern
            :: Pattern Variable -> StuckVerification (Pattern Variable) claim
        wrapStuckPattern stuckDescription =
            StuckVerification { stuckDescription, provenClaims }

verifyClaim
    :: forall claim m
    .  (MonadCatch m, MonadSimplify m)
    => ProofState claim (Pattern Variable) ~ CommonProofState
    => Claim claim
    => Show claim
    => Show (Rule claim)
    => Limit Natural
    -> GraphSearchOrder
    -> AllClaims claim
    -> Axioms claim
    -> (claim, Limit Natural)
    -> ExceptT (Pattern Variable) m ()
verifyClaim
    breadthLimit
    searchOrder
    (AllClaims claims)
    (Axioms axioms)
    (goal, depthLimit)
  =
    traceExceptT D_OnePath_verifyClaim [debugArg "rule" goal] $ do
    let
        startPattern = ProofState.Goal $ getConfiguration goal
        destination = getDestination goal
        limitedStrategy =
            Limit.takeWithin
                depthLimit
                (Foldable.toList $ strategy goal claims axioms)
    executionGraph <-
        runStrategyWithSearchOrder
            breadthLimit
            (modifiedTransitionRule destination)
            limitedStrategy
            searchOrder
            startPattern
    -- Throw the first unproven configuration as an error.
    Foldable.traverse_ Monad.Except.throwError (unprovenNodes executionGraph)
  where
    modifiedTransitionRule
        :: RHS Variable
        -> Prim claim
        -> CommonProofState
        -> TransitionT (Rule claim) (Verifier m) CommonProofState
    modifiedTransitionRule destination prim proofState' = do
        transitions <-
            lift . lift . runTransitionT
            $ transitionRule' goal destination prim proofState'
        Transition.scatter transitions

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
        (transitionRule' target destination)
        strategy'
        eg
        node
  where
    strategy' :: Strategy (Prim claim)
    strategy'
        | isRoot = firstStep
        | otherwise = followupStep

    firstStep :: Strategy (Prim claim)
    firstStep = strategy target claims axioms Stream.!! 0

    followupStep :: Strategy (Prim claim)
    followupStep = strategy target claims axioms Stream.!! 1

    isRoot :: Bool
    isRoot = node == root

transitionRule'
    :: forall claim m
    .  (MonadCatch m, MonadSimplify m)
    => Claim claim
    => claim
    -> RHS Variable
    -> Prim claim
    -> CommonProofState
    -> TransitionT (Rule claim) m CommonProofState
transitionRule' ruleType destination prim state = do
    let goal = flip (configurationDestinationToRule ruleType) destination <$> state
    next <- transitionRule prim goal
    pure $ fmap getConfiguration next
