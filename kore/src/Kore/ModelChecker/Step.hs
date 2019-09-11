{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.ModelChecker.Step
    ( -- * Primitive strategies
      Prim (..)
    , ModalPattern (..)
    , CommonModalPattern
    , ProofState (..)
    , CommonProofState
    , Transition
    , transitionRule
    , defaultOneStepStrategy
    ) where

import Control.Applicative
    ( Alternative (..)
    )
import Control.Monad
    ( when
    )
import Control.Monad.State.Strict
    ( StateT
    )
import qualified Control.Monad.State.Strict as State
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import Data.Hashable
import Data.Maybe
    ( isJust
    )
import Data.Text
    ( Text
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import GHC.Generics

import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
    ( TermLike
    )
import Kore.ModelChecker.Simplification
    ( checkImplicationIsTop
    )
import qualified Kore.Step.Result as StepResult
import Kore.Step.Rule
    ( RewriteRule (RewriteRule)
    , allPathGlobally
    )
import qualified Kore.Step.Simplification.Pattern as Pattern
    ( simplifyAndRemoveTopExists
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
    ( filterMultiOr
    )
import qualified Kore.Step.Step as Step
import Kore.Step.Strategy
    ( Strategy
    , TransitionT
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Syntax.Variable
    ( Variable
    )
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Unify as Monad.Unify
import Kore.Unparser

data Prim patt rewrite =
      CheckProofState
    -- ^ Check the proof state and decide whether to terminate the computation
    | Simplify
    -- ^ Builtin and function symbol simplification step
    | Unroll !patt
    -- ^ Unroll the proof goal
    | ComputeWeakNext ![rewrite]
    -- ^ Compute next states
    deriving (Show)

data ModalPattern variable = ModalPattern
    { modalOp :: !Text
    , term  :: !(TermLike variable)
    }

deriving instance Eq variable => Eq (ModalPattern variable)
deriving instance Show variable => Show (ModalPattern variable)

type CommonModalPattern = ModalPattern Variable

data ProofState patt
    = Proven
    | Unprovable !patt
    | GoalLHS !patt
    -- ^ State on which a normal 'Rewrite' can be applied. Also used
    -- for the start patterns.
    | GoalRemLHS !patt
    -- ^ State which can't be rewritten anymore.
  deriving (Show, Eq, Ord, Generic)

-- | A 'ProofState' instantiated to 'Pattern Variable' for convenience.
type CommonProofState = ProofState (Pattern Variable)

instance Hashable patt => Hashable (ProofState patt)

checkProofState :: Prim patt rewrite
checkProofState = CheckProofState

simplify :: Prim patt rewrite
simplify = Simplify

unroll :: patt -> Prim patt rewrite
unroll = Unroll

computeWeakNext :: [rewrite] -> Prim patt rewrite
computeWeakNext = ComputeWeakNext

type Transition m =
    TransitionT (RewriteRule Variable) (StateT (Maybe ()) m)

transitionRule
    :: forall m
    .  MonadSimplify m
    => Prim CommonModalPattern (RewriteRule Variable)
    -> CommonProofState
    -> Transition m CommonProofState
transitionRule
    strategyPrim
    proofState
  = case strategyPrim of
        CheckProofState -> transitionCheckProofState proofState
        Simplify -> transitionSimplify proofState
        Unroll goalrhs -> transitionUnroll goalrhs proofState
        ComputeWeakNext rewrites ->
            transitionComputeWeakNext rewrites proofState
  where
    transitionCheckProofState
        :: CommonProofState
        -> Transition m CommonProofState
    transitionCheckProofState proofState0 = do
        execState <- Monad.Trans.lift State.get
        -- End early if any unprovable state was reached
        when (isJust execState) empty
        case proofState0 of
            Proven -> empty
            Unprovable _ -> empty
            ps -> return ps

    transitionSimplify
        :: CommonProofState
        -> Transition m CommonProofState
    transitionSimplify Proven = return Proven
    transitionSimplify (Unprovable config) = return (Unprovable config)
    transitionSimplify (GoalLHS config) =
        applySimplify GoalLHS config
    transitionSimplify (GoalRemLHS config) =
        applySimplify GoalRemLHS config

    applySimplify wrapper config =
        do
            configs <-
                Monad.Trans.lift . Monad.Trans.lift
                $ Pattern.simplifyAndRemoveTopExists config
            filteredConfigs <- SMT.Evaluator.filterMultiOr configs
            if null filteredConfigs
                then return Proven
                else Foldable.asum (pure . wrapper <$> filteredConfigs)

    transitionUnroll
        :: CommonModalPattern
        -> CommonProofState
        -> Transition m CommonProofState
    transitionUnroll _ Proven = empty
    transitionUnroll _ (Unprovable _) = empty
    transitionUnroll goalrhs (GoalLHS config)
        | Pattern.isBottom config = return Proven
        | otherwise = applyUnroll goalrhs GoalLHS config
    transitionUnroll goalrhs (GoalRemLHS config)
        | Pattern.isBottom config = return Proven
        | otherwise = applyUnroll goalrhs GoalRemLHS config

    applyUnroll ModalPattern { modalOp, term } wrapper config
        | modalOp == allPathGlobally = do
            result <-
                Monad.Trans.lift . Monad.Trans.lift
                $ checkImplicationIsTop config term
            if result
                then return (wrapper config)
                else do
                    (Monad.Trans.lift . State.put) (Just ())
                    return (Unprovable config)
        | otherwise = (error . show . Pretty.vsep)
                      [ "Not implemented error:"
                      , "We don't know how to unroll the modalOp:"
                      , Pretty.pretty modalOp
                      ]

    transitionComputeWeakNext
        :: [RewriteRule Variable]
        -> CommonProofState
        -> Transition m CommonProofState
    transitionComputeWeakNext _ Proven = return Proven
    transitionComputeWeakNext _ (Unprovable config) = return (Unprovable config)
    transitionComputeWeakNext rules (GoalLHS config)
      = transitionComputeWeakNextHelper rules config
    transitionComputeWeakNext _ (GoalRemLHS _)
      = return (GoalLHS Pattern.bottom)

    transitionComputeWeakNextHelper
        :: [RewriteRule Variable]
        -> Pattern Variable
        -> Transition m CommonProofState
    transitionComputeWeakNextHelper _ config
        | Pattern.isBottom config = return Proven
    transitionComputeWeakNextHelper rules config = do
        eitherResults <-
            Monad.Trans.lift . Monad.Trans.lift
            $ Monad.Unify.runUnifierT
            $ Step.applyRewriteRulesParallel
                (Step.UnificationProcedure Unification.unificationProcedure)
                rules
                config
        case eitherResults of
            Left _ ->
                (error . show . Pretty.vsep)
                [ "Not implemented error:"
                , "while applying a \\rewrite axiom to the pattern:"
                , Pretty.indent 4 (unparse config)
                ,   "We decided to end the execution because we don't \
                    \understand this case well enough at the moment."
                ]
            Right results -> do
                let
                    mapRules =
                        StepResult.mapRules
                        $ RewriteRule
                        . Step.unwrapRule
                        . Step.withoutUnification
                    mapConfigs =
                        StepResult.mapConfigs
                            GoalLHS
                            GoalRemLHS
                StepResult.transitionResults
                    (mapConfigs $ mapRules (StepResult.mergeResults results))

defaultOneStepStrategy
    :: patt
    -- ^ The modal pattern.
    -> [rewrite]
    -- ^ normal rewrites
    -> Strategy (Prim patt rewrite)
defaultOneStepStrategy goalrhs rewrites =
    Strategy.sequence
        [ Strategy.apply checkProofState
        , Strategy.apply simplify
        , Strategy.apply (unroll goalrhs)
        , Strategy.apply (computeWeakNext rewrites)
        , Strategy.apply simplify
        ]
