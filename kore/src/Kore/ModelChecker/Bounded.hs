{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.ModelChecker.Bounded
    ( CheckResult (..)
    , Axiom (..)
    , bmcStrategy
    , checkClaim
    ) where

import Prelude.Kore

import Control.Monad.Catch
    ( MonadThrow
    )
import qualified Control.Monad.State.Strict as State
import qualified Data.Graph.Inductive.Graph as Graph
import Data.Limit
    ( Limit (..)
    )
import qualified Data.Limit as Limit
import qualified Data.Text as Text

import Kore.Internal.Pattern as Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
import Kore.ModelChecker.Step
    ( CommonModalPattern
    , CommonProofState
    , ModalPattern (..)
    , Prim (..)
    , defaultOneStepStrategy
    )
import qualified Kore.ModelChecker.Step as ProofState
    ( ProofState (..)
    )
import qualified Kore.ModelChecker.Step as ModelChecker
    ( Transition
    , transitionRule
    )
import Kore.Step.RulePattern
    ( ImplicationRule (ImplicationRule)
    , RHS (..)
    , RewriteRule
    , RulePattern (..)
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    )
import Kore.Step.Strategy
    ( ExecutionGraph (..)
    , GraphSearchOrder
    , Strategy
    , pickFinal
    , runStrategyWithSearchOrder
    )
import qualified Log
import Numeric.Natural
    ( Natural
    )

data CheckResult patt
    = Proved
    -- ^ Property is proved within the bound.
    | Failed !patt
    -- ^ Counter example is found within the bound.
    | Unknown
    -- ^ Result is unknown within the bound.
    deriving (Show)

newtype Axiom = Axiom { unAxiom :: RewriteRule VariableName }

bmcStrategy
    :: [Axiom]
    -> CommonModalPattern
    -> [Strategy (Prim CommonModalPattern (RewriteRule VariableName))]
bmcStrategy
    axioms
    goal
  =  repeat (defaultOneStepStrategy goal rewrites)
  where
    rewrites :: [RewriteRule VariableName]
    rewrites = map unwrap axioms
      where
        unwrap (Axiom a) = a

checkClaim
    :: forall m
    .  (MonadSimplify m, MonadThrow m)
    => Limit Natural
    ->  (  CommonModalPattern
        -> [Strategy (Prim CommonModalPattern (RewriteRule VariableName))]
        )
    -- ^ Creates a one-step strategy from a target pattern. See
    -- 'defaultStrategy'.
    -> GraphSearchOrder
    -> (ImplicationRule VariableName, Limit Natural)
    -- a claim to check, together with a maximum number of verification steps
    -- for each.
    -> m (CheckResult (TermLike VariableName))
checkClaim
    breadthLimit
    strategyBuilder
    searchOrder
    (ImplicationRule RulePattern { left, rhs = RHS { right } }, depthLimit)
  = do
        let
            ApplyAlias_ Alias { aliasConstructor = alias } [prop] = right
            goalPattern = ModalPattern { modalOp = getId alias, term = prop }
            strategy =
                Limit.takeWithin
                    depthLimit
                    (strategyBuilder goalPattern)
            startState :: CommonProofState
            startState =
                ProofState.GoalLHS
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

        Log.logInfo . Text.pack
            $ ("searched states: " ++ (show . Graph.order . graph $ executionGraph))

        let
            finalResult = (checkFinalNodes . pickFinal) executionGraph
        return finalResult
  where
    transitionRule'
        :: Prim CommonModalPattern (RewriteRule VariableName)
        -> CommonProofState
        -> ModelChecker.Transition m CommonProofState
    transitionRule' = ModelChecker.transitionRule

    checkFinalNodes
        :: [CommonProofState]
        -> CheckResult (TermLike VariableName)
    checkFinalNodes nodes = foldl' checkFinalNodesHelper Proved nodes
      where
        checkFinalNodesHelper Proved  ProofState.Proven = Proved
        checkFinalNodesHelper Proved  (ProofState.Unprovable config) =
            Failed (Pattern.toTermLike config)
        checkFinalNodesHelper Proved  _ = Unknown
        checkFinalNodesHelper Unknown (ProofState.Unprovable config) =
            Failed (Pattern.toTermLike config)
        checkFinalNodesHelper Unknown _ = Unknown
        checkFinalNodesHelper (Failed config) _ = Failed config
