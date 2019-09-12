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

import qualified Control.Monad.State.Strict as State
import qualified Data.Foldable as Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import Data.Limit
    ( Limit
    )
import qualified Data.Limit as Limit
import qualified Data.Text as Text

import Kore.Internal.Pattern
    ( Conditional (Conditional)
    )
import Kore.Internal.Pattern as Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import qualified Kore.Logger as Logger
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
import qualified Kore.Predicate.Predicate as Predicate
import Kore.Step.Rule
    ( ImplicationRule (ImplicationRule)
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
import Kore.Syntax.Id
    ( Id (..)
    )
import Kore.Syntax.Variable
    ( Variable
    )
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

newtype Axiom = Axiom { unAxiom :: RewriteRule Variable }

bmcStrategy
    :: [Axiom]
    -> CommonModalPattern
    -> [Strategy (Prim CommonModalPattern (RewriteRule Variable))]
bmcStrategy
    axioms
    goal
  =  repeat (defaultOneStepStrategy goal rewrites)
  where
    rewrites :: [RewriteRule Variable]
    rewrites = map unwrap axioms
      where
        unwrap (Axiom a) = a

checkClaim
    :: forall m
    .  MonadSimplify m
    =>  (  CommonModalPattern
        -> [Strategy (Prim CommonModalPattern (RewriteRule Variable))]
        )
    -- ^ Creates a one-step strategy from a target pattern. See
    -- 'defaultStrategy'.
    -> GraphSearchOrder
    -> (ImplicationRule Variable, Limit Natural)
    -- a claim to check, together with a maximum number of verification steps
    -- for each.
    -> m (CheckResult (TermLike Variable))
checkClaim
    strategyBuilder
    searchOrder
    (ImplicationRule RulePattern { left, right }, stepLimit)
  = do
        let
            ApplyAlias_ Alias { aliasConstructor = alias } [prop] = right
            goalPattern = ModalPattern { modalOp = getId alias, term = prop }
            strategy =
                Limit.takeWithin
                    stepLimit
                    (strategyBuilder goalPattern)
            startState :: CommonProofState
            startState =
                ProofState.GoalLHS
                    Conditional
                        { term = left
                        , predicate = Predicate.makeTruePredicate
                        , substitution = mempty
                        }
        executionGraph <- State.evalStateT
                            (runStrategyWithSearchOrder
                                transitionRule'
                                strategy
                                searchOrder
                                startState)
                            Nothing

        Logger.withLogScope (Logger.Scope "BMCStats")
            . Logger.logInfo
            . Text.pack
            $ ("searched states: " ++ (show . Graph.order . graph $ executionGraph))

        let
            finalResult = (checkFinalNodes . pickFinal) executionGraph
        return finalResult
  where
    transitionRule'
        :: Prim CommonModalPattern (RewriteRule Variable)
        -> CommonProofState
        -> ModelChecker.Transition m CommonProofState
    transitionRule' = ModelChecker.transitionRule

    checkFinalNodes
        :: [CommonProofState]
        -> CheckResult (TermLike Variable)
    checkFinalNodes nodes
      = Foldable.foldl' checkFinalNodesHelper Proved nodes
      where
        checkFinalNodesHelper Proved  ProofState.Proven = Proved
        checkFinalNodesHelper Proved  (ProofState.Unprovable config) =
            Failed (Pattern.toTermLike config)
        checkFinalNodesHelper Proved  _ = Unknown
        checkFinalNodesHelper Unknown (ProofState.Unprovable config) =
            Failed (Pattern.toTermLike config)
        checkFinalNodesHelper Unknown _ = Unknown
        checkFinalNodesHelper (Failed config) _ = Failed config
