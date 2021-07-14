{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.ModelChecker.Bounded (
    CheckResult (..),
    Axiom (..),
    bmcStrategy,
    checkClaim,
) where

import qualified Control.Lens as Lens
import Control.Monad.Catch (
    MonadThrow,
 )
import qualified Control.Monad.State.Strict as State
import Data.Generics.Sum (
    _Ctor,
 )
import qualified Data.Graph.Inductive.Graph as Graph
import Data.Limit (
    Limit (..),
 )
import qualified Data.Limit as Limit
import qualified Data.Text as Text
import qualified GHC.Generics as GHC
import Kore.Internal.Pattern as Conditional (
    Conditional (..),
    mapVariables,
 )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
import Kore.ModelChecker.Step (
    CommonModalPattern,
    CommonProofState,
    ModalPattern (..),
    Prim (..),
    defaultOneStepStrategy,
 )
import qualified Kore.ModelChecker.Step as ModelChecker (
    Transition,
    transitionRule,
 )
import qualified Kore.ModelChecker.Step as ProofState (
    ProofState (..),
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    getRewritingTerm,
    resetConfigVariable,
 )
import Kore.Rewrite.RulePattern (
    ImplicationRule (ImplicationRule),
    RHS (..),
    RewriteRule,
    RulePattern (..),
    mapRuleVariables,
 )
import Kore.Rewrite.Strategy (
    ExecutionGraph (..),
    GraphSearchOrder,
    Strategy,
    pickFinal,
    runStrategyWithSearchOrder,
 )
import Kore.Simplify.Simplify (
    MonadSimplify,
 )
import qualified Log
import Numeric.Natural (
    Natural,
 )
import Prelude.Kore

data CheckResult patt claim
    = -- | Property is proved within the bound.
      Proved
    | -- | Counter example is found within the bound.
      Failed !patt
    | -- | Result is unknown within the bound.
      Unknown !claim
    deriving stock (Show, GHC.Generic)

newtype Axiom = Axiom {unAxiom :: RewriteRule RewritingVariableName}

bmcStrategy ::
    [Axiom] ->
    CommonModalPattern ->
    [Strategy (Prim CommonModalPattern (RewriteRule RewritingVariableName))]
bmcStrategy
    axioms
    goal =
        repeat (defaultOneStepStrategy goal rewrites)
      where
        rewrites :: [RewriteRule RewritingVariableName]
        rewrites = map unwrap axioms
          where
            unwrap (Axiom a) = a

checkClaim ::
    forall m.
    (MonadSimplify m, MonadThrow m) =>
    Limit Natural ->
    -- | Creates a one-step strategy from a target pattern. See
    -- 'defaultStrategy'.
    ( CommonModalPattern ->
      [Strategy (Prim CommonModalPattern (RewriteRule RewritingVariableName))]
    ) ->
    GraphSearchOrder ->
    (ImplicationRule RewritingVariableName, Limit Natural) ->
    -- a claim to check, together with a maximum number of verification steps
    -- for each.
    m
        ( CheckResult
            (TermLike VariableName)
            (ImplicationRule VariableName)
        )
checkClaim
    breadthLimit
    strategyBuilder
    searchOrder
    (rule@(ImplicationRule RulePattern{left, rhs = RHS{right}}), depthLimit) =
        do
            let ApplyAlias_ Alias{aliasConstructor = alias} [prop] = right
                goalPattern =
                    ModalPattern
                        { modalOp = getId alias
                        , term = prop & TermLike.mapVariables resetConfigVariable
                        }
                strategy =
                    Limit.takeWithin
                        depthLimit
                        (strategyBuilder goalPattern)
                startState :: CommonProofState
                startState =
                    ProofState.GoalLHS $
                        Conditional.mapVariables resetConfigVariable $
                            Conditional
                                { term = left
                                , predicate = Predicate.makeTruePredicate
                                , substitution = mempty
                                }
            executionGraph <-
                runStrategyWithSearchOrder
                    breadthLimit
                    transitionRule'
                    strategy
                    searchOrder
                    startState
                    & flip State.evalStateT Nothing

            Log.logInfo . Text.pack $
                ("searched states: " ++ (show . Graph.order . graph $ executionGraph))

            let finalResult =
                    (checkFinalNodes . pickFinal) executionGraph
                        & _Ctor @"Failed" Lens.%~ getRewritingTerm
                        & _Ctor @"Unknown" Lens.%~ mapRuleVariables (pure from)
            return finalResult
      where
        transitionRule' ::
            Prim CommonModalPattern (RewriteRule RewritingVariableName) ->
            CommonProofState ->
            ModelChecker.Transition m CommonProofState
        transitionRule' = ModelChecker.transitionRule

        checkFinalNodes ::
            [CommonProofState] ->
            CheckResult
                (TermLike RewritingVariableName)
                (ImplicationRule RewritingVariableName)
        checkFinalNodes nodes = foldl' checkFinalNodesHelper Proved nodes
          where
            checkFinalNodesHelper Proved ProofState.Proven = Proved
            checkFinalNodesHelper Proved (ProofState.Unprovable config) =
                Failed (Pattern.toTermLike config)
            checkFinalNodesHelper Proved _ = Unknown rule
            checkFinalNodesHelper (Unknown _) (ProofState.Unprovable config) =
                Failed (Pattern.toTermLike config)
            checkFinalNodesHelper (Unknown _) _ = Unknown rule
            checkFinalNodesHelper (Failed config) _ = Failed config
