module Test.Kore.AllPath where

import Test.Tasty

import           Control.Applicative
import qualified Data.Foldable as Foldable
import           Data.Function
                 ( (&) )
import           Data.Functor.Identity
import qualified Data.Graph.Inductive as Gr
import           Data.Sequence
                 ( Seq )
import qualified Data.Sequence as Seq
import           GHC.Stack
                 ( HasCallStack )

import qualified Kore.AllPath as AllPath
import qualified Kore.Step.Representation.MultiOr as MultiOr
import qualified Kore.Step.Strategy as Strategy
import           Kore.Step.Transition
                 ( runTransitionT )
import qualified Kore.Step.Transition as Transition

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions
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

{- | @Goal@ is a simple goal for unit testing.

The goal is a pair of integers. It is considered proven when the left-hand side
and the right-hand side are equal. The destination is removed by subtraction.

 -}
type Goal = (Integer, Integer)

type ProofState = AllPath.ProofState Goal

data Rule = Divide Integer
    deriving (Eq, Ord, Show)

instance EqualWithExplanation Rule where
    compareWithExplanation = sumCompareWithExplanation
    printWithExplanation = show

instance SumEqualWithExplanation Rule where
    sumConstructorPair (Divide a1) (Divide a2) =
        SumConstructorSameWithArguments (EqWrap "Divide" a1 a2)

type Prim = AllPath.Prim Rule

-- | The destination-removal rule for our unit test goal.
removeDestination :: Monad m => Goal -> m Goal
removeDestination (src, dst) = return (src - dst, dst)

-- | The goal is trivially valid when the members are equal.
triviallyValid :: Goal -> Bool
triviallyValid (src, dst) = src == dst

derivePar :: [Rule] -> Goal -> Strategy.TransitionT Rule m ProofState
derivePar rules (src, dst) = Foldable.asum (deriveParWorker <$> rules)
  where
    deriveParWorker rule@(Divide n) = do
        let (q, r) = src `quotRem` n
            goal = do
                Transition.addRule rule
                pure (AllPath.Goal (q, dst))
            goalRem = pure (AllPath.GoalRem (r, dst))
        goal <|> goalRem

runTransitionRule :: Prim -> ProofState -> [(ProofState, Seq Rule)]
runTransitionRule prim state =
    (runIdentity . runTransitionT) (transitionRule prim state)

-- | 'AllPath.transitionRule' instantiated with our unit test rules.
transitionRule
    :: Prim
    -> ProofState
    -> Strategy.TransitionT Rule Identity ProofState
transitionRule =
    AllPath.transitionRule
        removeDestination
        triviallyValid
        derivePar

test_transitionRule_CheckProven :: [TestTree]
test_transitionRule_CheckProven =
    [ done AllPath.Proven
    , unmodified (AllPath.Goal    (2, 1))
    , unmodified (AllPath.GoalRem (2, 1))
    ]
  where
    run = runTransitionRule AllPath.CheckProven
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    done :: HasCallStack => ProofState -> TestTree
    done state = run state `satisfies_` Foldable.null

test_transitionRule_CheckGoalRem :: [TestTree]
test_transitionRule_CheckGoalRem =
    [ unmodified AllPath.Proven
    , unmodified (AllPath.Goal    (2, 1))
    , done       (AllPath.GoalRem undefined)
    ]
  where
    run = runTransitionRule AllPath.CheckGoalRem
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    done :: HasCallStack => ProofState -> TestTree
    done state = run state `satisfies_` Foldable.null

test_transitionRule_RemoveDestination :: [TestTree]
test_transitionRule_RemoveDestination =
    [ unmodified AllPath.Proven
    , unmodified (AllPath.GoalRem (2, 1))
    , run (AllPath.Goal (2, 1)) `equals` [(AllPath.GoalRem (1, 1), mempty)]  $ "removes destination from goal"
    ]
  where
    run = runTransitionRule AllPath.RemoveDestination
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]

test_transitionRule_TriviallyValid :: [TestTree]
test_transitionRule_TriviallyValid =
    [ unmodified    AllPath.Proven
    , unmodified    (AllPath.Goal    (2, 1))
    , unmodified    (AllPath.GoalRem (2, 1))
    , becomesProven (AllPath.GoalRem (1, 1))
    ]
  where
    run = runTransitionRule AllPath.TriviallyValid
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    becomesProven :: HasCallStack => ProofState -> TestTree
    becomesProven state = run state `equals_` [(AllPath.Proven, mempty)]

test_transitionRule_DerivePar :: [TestTree]
test_transitionRule_DerivePar =
    [ unmodified AllPath.Proven
    , unmodified (AllPath.Goal    (2, 1))
    , transits
        (AllPath.GoalRem (2, 1))
        [rule3]
        [ (AllPath.Goal    (0, 1), Seq.singleton rule3)
        , (AllPath.GoalRem (2, 1), mempty)
        ]
    , transits
        (AllPath.GoalRem (2, 1))
        [rule2, rule3]
        [ (AllPath.Goal    (1, 1), Seq.singleton rule2)
        , (AllPath.GoalRem (0, 1), mempty)
        , (AllPath.Goal    (0, 1), Seq.singleton rule3)
        , (AllPath.GoalRem (2, 1), mempty)
        ]
    ]
  where
    rule2 = Divide 2
    rule3 = Divide 3
    run rules = runTransitionRule (AllPath.DerivePar rules)
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run [rule3] state `equals_` [(state, mempty)]
    transits
        :: HasCallStack
        => ProofState
        -- ^ initial state
        -> [Rule]
        -- ^ rules to apply in parallel
        -> [(ProofState, Seq Rule)]
        -- ^ transitions
        -> TestTree
    transits state rules = equals_ (run rules state)

test_runStrategy :: [TestTree]
test_runStrategy =
    [ proves
        [ ]
        [ Divide 2 ]
        (2, 1)
        "proves goal with only axiom"
    , proves
        [ Divide 2 ]
        [ Divide 2 ]
        (2, 1)
        "proves goal with claim and axiom"
    , disproves
        [ ]
        [ ]
        (2, 1)
        [(2, 1)]
        "disproves goal with no claims or axioms"
    , disproves
        [ Divide 2 ]
        [ ]
        (2, 1)
        [(2, 1)]
        "disproves goal with no axioms"
    , disproves
        [ Divide 3 ]
        [ Divide 3 ]
        (2, 1)
        [(2, 1)]
        "disproves goal with relatively prime axiom and claim"
    ]
  where
    run claims axioms goal =
        runIdentity
        $ Strategy.runStrategy
            transitionRule
            (AllPath.strategy claims axioms)
            (AllPath.Goal goal)
    disproves
        :: HasCallStack
        => [Rule]
        -> [Rule]
        -> Goal
        -> [Goal]
        -- ^ unproven goals
        -> String
        -> TestTree
    disproves claims axioms goal unproven =
        equals
            (Foldable.toList $ AllPath.unprovenNodes $ run claims axioms goal)
            unproven
    proves :: HasCallStack => [Rule] -> [Rule] -> Goal -> String -> TestTree
    proves claims axioms goal =
        satisfies
            (run claims axioms goal)
            AllPath.proven
