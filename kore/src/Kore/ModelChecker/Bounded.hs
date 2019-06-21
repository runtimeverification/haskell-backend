{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.ModelChecker.Bounded
    ( CheckResult (..)
    , bmcStrategy
    , check
    ) where

import qualified Control.Monad.State.Strict as State
import qualified Data.Foldable as Foldable
import qualified Data.Graph.Inductive.Graph as Graph
import           Data.Limit
                 ( Limit )
import qualified Data.Limit as Limit
-- TODO (thomas.tuegel): Remove Debug.Trace
import Debug.Trace

import           Kore.Internal.Pattern
                 ( Conditional (Conditional) )
import           Kore.Internal.Pattern as Conditional
                 ( Conditional (..) )
import           Kore.Internal.TermLike
import           Kore.ModelChecker.Step
                 ( CommonModalPattern, CommonProofState, ModalPattern (..),
                 Prim (..), defaultOneStepStrategy )
import qualified Kore.ModelChecker.Step as ProofState
                 ( ProofState (..) )
import qualified Kore.ModelChecker.Step as ModelChecker
                 ( Transition, transitionRule )
import           Kore.OnePath.Verification
                 ( Axiom (Axiom) )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Rule
                 ( ImplicationRule (ImplicationRule), RewriteRule,
                 RulePattern (..) )
import           Kore.Step.Simplification.Data
                 ( MonadSimplify )
import           Kore.Step.Strategy
                 ( ExecutionGraph (..), GraphSearchOrder, Strategy, pickFinal,
                 runStrategyWithSearchOrder )
import           Kore.Syntax.Id
                 ( Id (..) )
import           Kore.Syntax.Variable
                 ( Variable )
import           Numeric.Natural
                 ( Natural )

data CheckResult
    = Proved
    -- ^ Property is proved within the bound.
    | Failed
    -- ^ Counter example is found within the bound.
    | Unknown
    -- ^ Result is unknown within the bound.
    deriving (Show)

check
    :: MonadSimplify m
    =>  (  CommonModalPattern
        -> [Strategy
            (Prim
                (CommonModalPattern)
                (RewriteRule Variable)
            )
           ]
        )
    -- ^ Creates a one-step strategy from a target pattern. See
    -- 'defaultStrategy'.
    -> GraphSearchOrder
    -> [(ImplicationRule Variable, Limit Natural)]
    -- ^ List of claims, together with a maximum number of verification steps
    -- for each.
    -> m [CheckResult]
check strategyBuilder searchOrder =
    mapM (checkClaim strategyBuilder searchOrder)

bmcStrategy
    :: [Axiom]
    -> CommonModalPattern
    -> [Strategy (Prim (CommonModalPattern) (RewriteRule Variable))]
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
        -> [Strategy
            (Prim
                (CommonModalPattern)
                (RewriteRule Variable)
            )
           ]
        )
    -> GraphSearchOrder
    -> (ImplicationRule Variable, Limit Natural)
    -> m CheckResult
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
        traceM ("searched states: " ++ (show . Graph.order . graph $ executionGraph))
        let
            finalResult = (checkFinalNodes . pickFinal) executionGraph
        trace (show finalResult) (return finalResult)
  where
    transitionRule'
        :: Prim (CommonModalPattern) (RewriteRule Variable)
        -> (CommonProofState)
        -> ModelChecker.Transition m CommonProofState
    transitionRule' = ModelChecker.transitionRule

    checkFinalNodes
        :: [CommonProofState]
        -> CheckResult
    checkFinalNodes nodes
      = Foldable.foldl' checkFinalNodesHelper Proved nodes
      where
        checkFinalNodesHelper Proved  ProofState.Proven = Proved
        checkFinalNodesHelper Proved  ProofState.Unprovable = Failed
        checkFinalNodesHelper Proved  _ = Unknown
        checkFinalNodesHelper Unknown ProofState.Unprovable = Failed
        checkFinalNodesHelper Unknown _ = Unknown
        checkFinalNodesHelper Failed  _ = Failed
