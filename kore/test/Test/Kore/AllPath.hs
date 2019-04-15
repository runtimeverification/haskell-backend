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

instance EqualWithExplanation K where
    compareWithExplanation = rawCompareWithExplanation
    printWithExplanation = show

type Goal = (K, K)

type ProofState = AllPath.ProofState Goal

type Rule = (K, K)

ruleAC :: Rule
ruleAC = (A, C)

cyclicRule :: [Rule]
cyclicRule = [(A, A)]

ruleAB, ruleAF :: Rule
ruleAB = (A, B)
ruleAF = (A, F)

ruleBC, ruleBD, ruleBF :: Rule
ruleBC = (B, C)
ruleBD = (B, D)
ruleBF = (B, F)

ruleCD, ruleCF :: Rule
ruleCD = (C, D)
ruleCF = (C, F)

ruleDE :: Rule
ruleDE = (D, E)

ruleEF :: Rule
ruleEF = (E, F)

noRules :: [Rule]
noRules = []

oneRule :: [Rule]
oneRule = [ruleAB]

concurrentRules :: [Rule]
concurrentRules = [ ruleAB, ruleAC ]

differentLengthPaths :: [Rule]
differentLengthPaths =
    [ ruleAB
    , ruleAF
    , ruleBC
    , ruleBD
    , ruleBF
    , ruleCD
    , ruleCF
    , ruleDE
    , ruleEF
    ]

type Prim = AllPath.Prim Rule

-- | The destination-removal rule for our unit test goal.
removeDestination :: Monad m => Goal -> m Goal
removeDestination (src, dst) =
    return (src', dst)
  where
    src'
      | dst == src        = Bot
      | src `matches` dst = Bot
      | B    <- dst, BorC <- src = C
      | C    <- dst, BorC <- src = B
      | otherwise  = src

-- | The goal is trivially valid when the members are equal.
triviallyValid :: Goal -> Bool
triviallyValid (src, _) = src == Bot

derivePar :: [Rule] -> Goal -> Strategy.TransitionT Rule m ProofState
derivePar rules (src, dst) =
    goals <|> goalRem
  where
    goalRem
      | any Maybe.isJust applied = (pure . AllPath.GoalRem) (Bot, dst)
      | otherwise = (pure . AllPath.GoalRem) (src, dst)
    applied = applyRule <$> rules
    applyRule rule@(from, to)
      | src `matches` from = Just $ do
        Transition.addRule rule
        (pure . AllPath.Goal) (to, dst)
      | otherwise   = Nothing
    goals = Foldable.asum (Maybe.fromMaybe empty <$> applied)

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
    , run (AllPath.Goal (B, B)) `equals` [(AllPath.GoalRem (Bot, B), mempty)]  $ "removes destination from goal"
    ]
  where
    run = runTransitionRule AllPath.RemoveDestination
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]

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
    , transits
        (AllPath.GoalRem (B, C))
        [ruleBC]
        [ (AllPath.Goal    (C, C), Seq.singleton ruleBC)
        , (AllPath.GoalRem (Bot, C), mempty)
        ]
    , transits
        (AllPath.GoalRem (A, B))
        [ruleAB, ruleBC]
        [ (AllPath.Goal    (B  , B), Seq.singleton ruleAB)
        , (AllPath.GoalRem (Bot, B), mempty)
        ]
    ]
  where
    run rules = runTransitionRule (AllPath.DerivePar rules)
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run oneRule state `equals_` [(state, mempty)]
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
    [ proves    noRules (A, A) "identity"
    , disproves noRules (A, B) "no claims or axioms" [(A, B)]

    , proves    oneRule (A, B   ) "only axiom"
    , proves    oneRule (A, BorC) "disjoint goal"
    , disproves oneRule (A, C   ) "partial progess toward goal" [(B, C)]

    , proves    cyclicRule (A, B) "cyclic rule"
    , proves    cyclicRule (A, C) "cyclic rule"

    , proves    concurrentRules (A, BorC) "concurrent rules"
    , disproves concurrentRules (A, B   ) "concurrent rules" [(C, B)]

    , proves    differentLengthPaths (A, F) "paths of different length"
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
        -> String
        -- ^ Message
        -> [Goal]
        -- ^ Unproven goals
        -> TestTree
    disproves axioms goal message unproven =
        equals
            (Foldable.toList $ AllPath.unprovenNodes $ run axioms goal)
            unproven
            ("disproves goal with " <> message)
    proves
        :: HasCallStack
        => [Rule]
        -- ^ Axioms
        -> Goal
        -- ^ Proof goal
        -> String
        -> TestTree
    proves axioms goal message =
        satisfies
            (run axioms goal)
            AllPath.proven
            ("proves goal with " <> message)
