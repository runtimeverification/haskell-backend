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
    , transitionRule
    , defaultOneStepStrategy
    ) where

import           Control.Applicative
                 ( Alternative (..) )
import qualified Control.Monad.Trans as Monad.Trans
import qualified Data.Foldable as Foldable
import           Data.Hashable
import           Data.Text
                 ( Text )
import qualified Data.Text.Prettyprint.Doc as Pretty
import           Debug.Trace
import           GHC.Generics

import           Kore.AST.Common
                 ( Variable )
import           Kore.AST.MetaOrObject
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.ModelChecker.Simplification
                 ( checkImplicationIsTop )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Pattern
                 ( StepPattern )
import           Kore.Step.Representation.ExpandedPattern
                 ( CommonExpandedPattern )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
import qualified Kore.Step.Result as StepResult
import           Kore.Step.Rule
                 ( RewriteRule (RewriteRule) )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, Simplifier,
                 StepPatternSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
                 ( simplify )
import qualified Kore.Step.Step as Step
import           Kore.Step.Strategy
                 ( Strategy, TransitionT )
import qualified Kore.Step.Strategy as Strategy
import qualified Kore.Unification.Procedure as Unification
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser

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

data ModalPattern level variable = ModalPattern
    { modalOp :: !Text
    , term  :: !(StepPattern level variable)
    } deriving (Eq, Show)

type CommonModalPattern level = ModalPattern level Variable

data ProofState patt
    = Proven
    | Unprovable
    | GoalLHS !patt
    -- ^ State on which a normal 'Rewrite' can be applied. Also used
    -- for the start patterns.
    | GoalRemLHS !patt
    -- ^ State which can't be rewritten anymore.
  deriving (Show, Eq, Ord, Generic)

-- | A 'ProofState' instantiated to 'CommonExpandedPattern' for convenience.
type CommonProofState level = ProofState (CommonExpandedPattern level)

instance Hashable patt => Hashable (ProofState patt)

checkProofState :: Prim patt rewriteResult
checkProofState = CheckProofState

simplify :: Prim patt rewrite
simplify = Simplify

unroll :: patt -> Prim patt rewrite
unroll = Unroll

computeWeakNext :: [rewrite] -> Prim patt rewrite
computeWeakNext = ComputeWeakNext

type Transition = TransitionT (RewriteRule Object Variable) Simplifier

transitionRule
    :: forall level . (MetaOrObject level)
    => SmtMetadataTools StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions in patterns
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
    -> Prim (CommonModalPattern level) (RewriteRule level Variable)
    -> CommonProofState level
    -> Transition
        (CommonProofState level)
transitionRule
    tools
    predicateSimplifier
    patternSimplifier
    axiomSimplifiers
    strategyPrim
    proofState
  =
    case strategyPrim of
        CheckProofState -> transitionCheckProofState proofState
        Simplify -> transitionSimplify proofState
        Unroll goalrhs -> transitionUnroll goalrhs proofState
        ComputeWeakNext rewrites -> transitionComputeWeakNext rewrites proofState
  where
    transitionCheckProofState
        :: CommonProofState level
        -> TransitionT (RewriteRule level Variable) Simplifier
            (CommonProofState level )
    transitionCheckProofState Proven = empty
    transitionCheckProofState Unprovable = empty
    transitionCheckProofState ps = return ps

    transitionSimplify
        :: CommonProofState level
        -> TransitionT (RewriteRule level Variable) Simplifier
            (CommonProofState level )
    transitionSimplify Proven = return Proven
    transitionSimplify Unprovable = return Unprovable
    transitionSimplify (GoalLHS config) =
        applySimplify GoalLHS config
    transitionSimplify (GoalRemLHS config) =
        applySimplify GoalRemLHS config

    applySimplify wrapper config =
        do
            (configs, _) <-
                Monad.Trans.lift
                $ ExpandedPattern.simplify
                    tools
                    predicateSimplifier
                    patternSimplifier
                    axiomSimplifiers
                    config
            let
                -- Filter out ⊥ patterns
                nonEmptyConfigs = MultiOr.filterOr configs
            if null nonEmptyConfigs
                then return Proven
                else Foldable.asum (pure <$> map wrapper (Foldable.toList nonEmptyConfigs))

    transitionUnroll
        :: CommonModalPattern level
        -> CommonProofState level
        -> TransitionT (RewriteRule level Variable) Simplifier
            (CommonProofState level )
    transitionUnroll _ Proven = empty
    transitionUnroll _ Unprovable = empty
    transitionUnroll goalrhs (GoalLHS config)
        | ExpandedPattern.isBottom config = return Proven
        | otherwise = applyUnroll goalrhs GoalLHS config
    transitionUnroll goalrhs (GoalRemLHS config)
        | ExpandedPattern.isBottom config = return Proven
        | otherwise = applyUnroll goalrhs GoalRemLHS config

    applyUnroll ModalPattern { modalOp, term } wrapper config
      = case modalOp of
            "ag" -> do
                result <-
                    Monad.Trans.lift
                    $ checkImplicationIsTop
                        tools
                        predicateSimplifier
                        patternSimplifier
                        axiomSimplifiers
                        config
                        term
                if result
                    then return (wrapper config)
                    else do
                        trace
                            (show . Pretty.vsep
                                $ [ "config failed to prove the invariant:"
                                  , Pretty.indent 4 (unparse config)
                                  ]
                            )
                            return Unprovable
            _ -> (error . show . Pretty.vsep)
                 [ "Not implemented error:"
                 , "We don't know how to unroll the modalOp:"
                 , Pretty.pretty modalOp
                 ]

    transitionComputeWeakNext
        :: [RewriteRule level Variable]
        -> CommonProofState level
        -> TransitionT (RewriteRule level Variable) Simplifier
            (CommonProofState level)
    transitionComputeWeakNext _ Proven = return Proven
    transitionComputeWeakNext _ Unprovable = return Unprovable
    transitionComputeWeakNext rules (GoalLHS config)
      = transitionComputeWeakNextHelper rules config
    transitionComputeWeakNext _ (GoalRemLHS _)
      = return (GoalLHS ExpandedPattern.bottom)

    transitionComputeWeakNextHelper
        :: [RewriteRule level Variable]
        -> (CommonExpandedPattern level)
        -> TransitionT (RewriteRule level Variable) Simplifier
            (CommonProofState level)
    transitionComputeWeakNextHelper _ config
        | ExpandedPattern.isBottom config = return Proven
    transitionComputeWeakNextHelper rules config = do
        result <-
            Monad.Trans.lift
            $ Monad.Unify.runUnifier
            $ Step.applyRewriteRules
                tools
                predicateSimplifier
                patternSimplifier
                axiomSimplifiers
                (Step.UnificationProcedure Unification.unificationProcedure)
                rules
                config
        case result of
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
                StepResult.transitionResults (mapConfigs $ mapRules results)

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
