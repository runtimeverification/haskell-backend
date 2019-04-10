module Test.Kore.AllPath where

import Test.Tasty

import qualified Data.Foldable as Foldable
import           Data.Function
                 ( (&) )
import           Data.Functor.Identity
import qualified Data.Graph.Inductive as Gr
import           Data.Sequence
                 ( Seq )

import qualified Kore.AllPath as AllPath
import qualified Kore.Step.Representation.MultiOr as MultiOr
import qualified Kore.Step.Strategy as Strategy
import           Kore.Step.Transition
                 ( runTransitionT )

import Test.Kore.Comparators ()
import Test.Terse

type ExecutionGraph = Strategy.ExecutionGraph (AllPath.ProofState Integer) ()

emptyExecutionGraph :: AllPath.ProofState Integer -> ExecutionGraph
emptyExecutionGraph = Strategy.emptyExecutionGraph

insNode
    :: (Gr.Node, AllPath.ProofState Integer)
    -> ExecutionGraph
    -> ExecutionGraph
insNode = Strategy.insNode

insEdge
    :: (Gr.Node, Gr.Node)
    -> ExecutionGraph
    -> ExecutionGraph
insEdge = Strategy.insEdge

test_unprovenNodes :: [TestTree]
test_unprovenNodes =
    [ AllPath.unprovenNodes
        (emptyExecutionGraph AllPath.Proven)
        `satisfies_`
        Foldable.null
    , AllPath.unprovenNodes
        (emptyExecutionGraph (AllPath.Goal 1))
        `satisfies_`
        (not . Foldable.null)
    , AllPath.unprovenNodes
        (emptyExecutionGraph (AllPath.Goal 1))
        `equals`
        (MultiOr.MultiOr [1])
        $  "returns single unproven node"
    , AllPath.unprovenNodes
        (emptyExecutionGraph (AllPath.Goal 0)
            & insNode (1, AllPath.Goal 1)
            & insNode (2, AllPath.Proven)
        )
        `equals_`
        (MultiOr.MultiOr [0, 1])
    , AllPath.unprovenNodes
        (emptyExecutionGraph (AllPath.Goal 0)
            & insNode (1, AllPath.Goal 1)
            & insEdge (0, 1)
            & insNode (2, AllPath.Proven)
            & insEdge (0, 2)
        )
        `equals_`
        (MultiOr.MultiOr [1])
    , AllPath.unprovenNodes
        (emptyExecutionGraph (AllPath.Goal 0)
            & insNode (1, AllPath.Goal 1)
            & insEdge (0, 1)
            & insNode (2, AllPath.Goal 2)
            & insEdge (1, 2)
            & insNode (3, AllPath.Proven)
            & insEdge (2, 3)
        )
        `equals_`
        (MultiOr.MultiOr [])
    , AllPath.unprovenNodes
        (emptyExecutionGraph (AllPath.Goal 0)
            & insNode (1, AllPath.GoalRem 1)
            & insEdge (0, 1)
            & insNode (2, AllPath.Proven)
            & insEdge (0, 2)
        )
        `equals_`
        (MultiOr.MultiOr [1])
    ]

transitionRule
    :: AllPath.Prim ()
    -> AllPath.ProofState Integer
    -> [(AllPath.ProofState Integer, Seq ())]
transitionRule prim state =
    (runIdentity . runTransitionT)
        (AllPath.transitionRule prim state)

test_transitionRule_CheckProven :: [TestTree]
test_transitionRule_CheckProven =
    [ run AllPath.Proven      `satisfies_` Foldable.null
    , run (AllPath.Goal 1   ) `equals_`    [(AllPath.Goal 1, mempty)]
    , run (AllPath.GoalRem 1) `equals_`    [(AllPath.GoalRem 1, mempty)]
    ]
  where
    run = transitionRule AllPath.CheckProven

test_transitionRule_RemoveDestination :: [TestTree]
test_transitionRule_RemoveDestination =
    [ run AllPath.Proven `equals_` [(AllPath.Proven, mempty)]
    ]
  where
    run = transitionRule AllPath.RemoveDestination
