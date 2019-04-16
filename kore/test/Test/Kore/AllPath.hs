module Test.Kore.AllPath where

import Test.Tasty

import           Control.Applicative
import qualified Data.Foldable as Foldable
import           Data.Function
                 ( (&) )
import           Data.Functor.Identity
import qualified Data.Graph.Inductive as Gr
import qualified Data.Maybe as Maybe
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

-- | Simple program configurations for unit testing.
data K = BorC | A | B | C | D | E | F | Bot
    deriving (Eq, Ord, Show)

matches :: K -> K -> Bool
matches B BorC = True
matches C BorC = True
matches a b    = a == b

difference :: K -> K -> K
difference BorC B = C
difference BorC C = B
difference a    b
  | a `matches` b = Bot
  | otherwise     = a

instance EqualWithExplanation K where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

type Goal = (K, K)

type ProofState = AllPath.ProofState Goal

type Rule = (K, K)

type Prim = AllPath.Prim Rule

runTransitionRule :: Prim -> ProofState -> [(ProofState, Seq Rule)]
runTransitionRule prim state =
    (runIdentity . runTransitionT) (transitionRule prim state)

-- | The destination-removal rule for our unit test goal.
removeDestination :: Monad m => Goal -> m Goal
removeDestination (src, dst) =
    return (difference src dst, dst)

-- | The goal is trivially valid when the members are equal.
triviallyValid :: Goal -> Bool
triviallyValid (src, _) = src == Bot

derivePar :: [Rule] -> Goal -> Strategy.TransitionT Rule m ProofState
derivePar rules (src, dst) =
    goals <|> goalRem
  where
    goal rule@(_, to) = do
        Transition.addRule rule
        (pure . AllPath.Goal) (to, dst)
    goalRem = do
        let r = Foldable.foldl' difference src (fst <$> applied)
        (pure . AllPath.GoalRem) (r, dst)
    applyRule rule@(from, _)
      | from `matches` src = Just rule
      | otherwise = Nothing
    applied = Maybe.mapMaybe applyRule rules
    goals = Foldable.asum (goal <$> applied)

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
    , unmodified (AllPath.Goal    (A, B))
    , unmodified (AllPath.GoalRem (A, B))
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
    , unmodified (AllPath.Goal    (A, B))
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
    , unmodified (AllPath.GoalRem (A, B))
    , AllPath.Goal (B, B) `becomes` (AllPath.GoalRem (Bot, B), mempty)
    ]
  where
    run = runTransitionRule AllPath.RemoveDestination
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    becomes initial final = run initial `equals_` [final]

test_transitionRule_TriviallyValid :: [TestTree]
test_transitionRule_TriviallyValid =
    [ unmodified    AllPath.Proven
    , unmodified    (AllPath.Goal    (A, B))
    , unmodified    (AllPath.GoalRem (A, B))
    , becomesProven (AllPath.GoalRem (Bot, B))
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
    , unmodified (AllPath.Goal    (A, B))
    , [(A, C)]
        `derives`
        [ (AllPath.Goal    (C,   C), Seq.singleton (A, C))
        , (AllPath.GoalRem (Bot, C), mempty)
        ]
    , [(A, B), (B, C)]
        `derives`
        [ (AllPath.Goal    (B  , C), Seq.singleton (A, B))
        , (AllPath.GoalRem (Bot, C), mempty)
        ]
    ]
  where
    run rules = runTransitionRule (AllPath.DerivePar rules)
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run [(A, B)] state `equals_` [(state, mempty)]
    derives
        :: HasCallStack
        => [Rule]
        -- ^ rules to apply in parallel
        -> [(ProofState, Seq Rule)]
        -- ^ transitions
        -> TestTree
    derives rules = equals_ (run rules $ AllPath.GoalRem (A, C))

test_runStrategy :: [TestTree]
test_runStrategy =
    [ [] `proves`    (A, A)
    , [] `disproves` (A, B) $ [(A, B)]

    , [(A, B)] `proves`    (A, B   )
    , [(A, B)] `proves`    (A, BorC)
    , [(A, B)] `disproves` (A, C   ) $ [(B, C)]

    , [(A, A)] `proves` (A, B)
    , [(A, A)] `proves` (A, C)

    , [(A, B), (A, C)] `proves`    (A, BorC)
    , [(A, B), (A, C)] `disproves` (A, B   ) $ [(C, B)]

    , differentLengthPaths `proves` (A, F)
    ]
  where
    run axioms goal =
        runIdentity
        $ Strategy.runStrategy
            transitionRule
            (AllPath.strategy [goal] axioms)
            (AllPath.Goal goal)
    disproves
        :: HasCallStack
        => [Rule]
        -- ^ Axioms
        -> Goal
        -- ^ Proof goal
        -> [Goal]
        -- ^ Unproven goals
        -> TestTree
    disproves axioms goal unproven =
        equals
            (Foldable.toList $ AllPath.unprovenNodes $ run axioms goal)
            unproven
            (show axioms ++ " disproves " ++ show goal)
    proves
        :: HasCallStack
        => [Rule]
        -- ^ Axioms
        -> Goal
        -- ^ Proof goal
        -> TestTree
    proves axioms goal =
        satisfies
            (run axioms goal)
            AllPath.proven
            (show axioms ++ " proves " ++ show goal)

differentLengthPaths :: [Rule]
differentLengthPaths =
    [ -- Length 5 path
      (A, B), (B, C), (C, D), (D, E), (E, F)
      -- Length 4 path
    ,                         (D, F)
      -- Length 3 path
    ,                 (C, F)
      -- Length 2 path
    ,         (B, F)
      -- Length 1 path
    , (A, F)
    ]
