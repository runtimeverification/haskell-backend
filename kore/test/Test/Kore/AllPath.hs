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

import qualified Kore.Goal as Goal
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Logger
                 ( LogMessage (..), WithLog (..) )
import           Kore.Profiler.Data
                 ( Configuration (..), MonadProfiler (..) )
import           Kore.Step.Simplification.Data
                 ( MonadSimplify (..) )
import qualified Kore.Step.Strategy as Strategy
import           Kore.Step.Transition
                 ( runTransitionT )
import qualified Kore.Step.Transition as Transition
import           SMT
                 ( MonadSMT (..) )

import Test.Kore.Comparators ()
import Test.Tasty.HUnit.Extensions
import Test.Terse
--
-- -- * Tests
--
test_unprovenNodes :: [TestTree]
test_unprovenNodes =
    [ Goal.unprovenNodes
        (emptyExecutionGraph Goal.Proven)
        `satisfies_`
        Foldable.null
    , Goal.unprovenNodes
        (goal 0)
        `satisfies_`
        (not . Foldable.null)
    , Goal.unprovenNodes
        (goal 0)
        `equals`
        MultiOr.MultiOr [0]
        $  "returns single unproven node"
    , Goal.unprovenNodes
        (goal 0
            & insNode (1, Goal.Goal 1)
            & insNode (2, Goal.Proven)
        )
        `equals_`
        MultiOr.MultiOr [0, 1]
    , Goal.unprovenNodes
        (goal 0
            & subgoal 0 (1, Goal.Goal 1)
            & subgoal 0 (2, Goal.Proven)
        )
        `equals_`
        MultiOr.MultiOr [1]
    , Goal.unprovenNodes
        (goal 0
            & subgoal 0 (1, Goal.Goal 1)
            & subgoal 1 (2, Goal.Goal 2)
            & subgoal 2 (3, Goal.Proven)
        )
        `equals_`
        MultiOr.MultiOr []
    , Goal.unprovenNodes
        (goal 0
            & subgoal 0 (1, Goal.GoalRem 1)
            & subgoal 0 (2, Goal.Proven)
        )
        `equals_`
        MultiOr.MultiOr [1]
    ]
  where
    goal :: Integer -> ExecutionGraph
    goal n = emptyExecutionGraph (Goal.Goal n)

    subgoal
        :: Gr.Node
        -> (Gr.Node, Goal.ProofState Integer)
        -> ExecutionGraph -> ExecutionGraph
    subgoal parent node@(child, _) =
        insEdge (parent, child) . insNode node

test_transitionRule_CheckProven :: [TestTree]
test_transitionRule_CheckProven =
    [ done Goal.Proven
    , unmodified (Goal.Goal    (A, B))
    , unmodified (Goal.GoalRem (A, B))
    ]
  where
    run = runTransitionRule Goal.CheckProven
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    done :: HasCallStack => ProofState -> TestTree
    done state = run state `satisfies_` Foldable.null

test_transitionRule_CheckGoalRem :: [TestTree]
test_transitionRule_CheckGoalRem =
    [ unmodified Goal.Proven
    , unmodified (Goal.Goal    (A, B))
    , done       (Goal.GoalRem undefined)
    ]
  where
    run = runTransitionRule Goal.CheckGoalRem
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    done :: HasCallStack => ProofState -> TestTree
    done state = run state `satisfies_` Foldable.null

test_transitionRule_RemoveDestination :: [TestTree]
test_transitionRule_RemoveDestination =
    [ unmodified Goal.Proven
    , unmodified (Goal.GoalRem (A, B))
    , Goal.Goal (B, B) `becomes` (Goal.GoalRem (Bot, B), mempty)
    ]
  where
    run = runTransitionRule Goal.RemoveDestination
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    becomes initial final = run initial `equals_` [final]

test_transitionRule_TriviallyValid :: [TestTree]
test_transitionRule_TriviallyValid =
    [ unmodified    Goal.Proven
    , unmodified    (Goal.Goal    (A, B))
    , unmodified    (Goal.GoalRem (A, B))
    , becomesProven (Goal.GoalRem (Bot, B))
    ]
  where
    run = runTransitionRule Goal.TriviallyValid
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    becomesProven :: HasCallStack => ProofState -> TestTree
    becomesProven state = run state `equals_` [(Goal.Proven, mempty)]

test_transitionRule_DerivePar :: [TestTree]
test_transitionRule_DerivePar =
    [ unmodified Goal.Proven
    , unmodified (Goal.Goal    (A, B))
    , [Rule (A, C)]
        `derives`
        [ (Goal.Goal    (C,   C), Seq.singleton $ Rule (A, C))
        , (Goal.GoalRem (Bot, C), mempty)
        ]
    , fmap Rule [(A, B), (B, C)]
        `derives`
        [ (Goal.Goal    (B  , C), Seq.singleton $ Rule (A, B))
        , (Goal.GoalRem (Bot, C), mempty)
        ]
    ]
  where
    run rules = runTransitionRule (Goal.DerivePar rules)
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run [Rule (A, B)] state `equals_` [(state, mempty)]
    derives
        :: HasCallStack
        => [Goal.Rule Goal]
        -- ^ rules to apply in parallel
        -> [(ProofState, Seq (Goal.Rule Goal))]
        -- ^ transitions
        -> TestTree
    derives rules = equals_ (run rules $ Goal.GoalRem (A, C))

test_runStrategy :: [TestTree]
test_runStrategy =
    [ [] `proves`    (A, A)
    , [] `disproves` (A, B) $ [(A, B)]

    , [Rule (A, Bot)] `proves` (A, A)
    , [Rule (A, Bot)] `proves` (A, B)

    , [Rule (A, B)] `proves`    (A, B   )
    , [Rule (A, B)] `proves`    (A, BorC)
    , [Rule (A, B)] `disproves` (A, C   ) $ [(B, C)]

    , [Rule (A, A)] `proves` (A, B)
    , [Rule (A, A)] `proves` (A, C)

    , fmap Rule [(A, B), (A, C)] `proves`    (A, BorC)
    , fmap Rule [(A, B), (A, C)] `disproves` (A, B   ) $ [(C, B)]

    , differentLengthPaths `proves` (A, F)
    ]
  where
    run
        :: [Goal.Rule Goal]
        -> Goal.Rule Goal
        -> Strategy.ExecutionGraph ProofState (Goal.Rule Goal)
    run axioms goal =
        runIdentity
        . unAllPathIdentity
        $ Strategy.runStrategy
            transitionRule
            (Goal.allPathStrategy [goal] axioms)
            (Goal.Goal . unRule $ goal)
    disproves
        :: HasCallStack
        => [Goal.Rule Goal]
        -- ^ Axioms
        -> Goal
        -- ^ Proof goal
        -> [Goal]
        -- ^ Unproven goals
        -> TestTree
    disproves axioms goal unproven =
        equals
            (Foldable.toList $ Goal.unprovenNodes $ run axioms (Rule goal))
            unproven
            (show axioms ++ " disproves " ++ show goal)
    proves
        :: HasCallStack
        => [Goal.Rule Goal]
        -- ^ Axioms
        -> Goal
        -- ^ Proof goal
        -> TestTree
    proves axioms goal =
        satisfies
            (run axioms (Rule goal))
            Goal.proven
            (show axioms ++ " proves " ++ show goal)

-- * Definitions

type ExecutionGraph = Strategy.ExecutionGraph (Goal.ProofState Integer) ()

emptyExecutionGraph :: Goal.ProofState Integer -> ExecutionGraph
emptyExecutionGraph = Strategy.emptyExecutionGraph

insNode
    :: (Gr.Node, Goal.ProofState Integer)
    -> ExecutionGraph
    -> ExecutionGraph
insNode = Strategy.insNode

insEdge
    :: (Gr.Node, Gr.Node)
    -> ExecutionGraph
    -> ExecutionGraph
insEdge = Strategy.insEdge

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

type ProofState = Goal.ProofState Goal

type Prim = Goal.Prim (Goal.Rule Goal)

instance Goal.Goal Goal where

    newtype Rule Goal =
        Rule { unRule :: (K, K) }
        deriving (Eq, Show, EqualWithExplanation)

    -- | The destination-removal rule for our unit test goal.
    removeDestination (src, dst) =
        return (difference src dst, dst)

    -- | The goal is trivially valid when the members are equal.
    isTriviallyValid (src, _) = src == Bot

    derivePar rules (src, dst) =
        goals <|> goalRem
      where
        goal rule@(Rule (_, to)) = do
            Transition.addRule rule
            (pure . Goal.Goal) (to, dst)
        goalRem = do
            let r = Foldable.foldl' difference src (fst . unRule <$> applied)
            (pure . Goal.GoalRem) (r, dst)
        applyRule rule@(Rule (from, _))
          | from `matches` src = Just rule
          | otherwise = Nothing
        applied = Maybe.mapMaybe applyRule rules
        goals = Foldable.asum (goal <$> applied)

    simplify = undefined
    isTrusted = undefined
    deriveSeq = Goal.derivePar

runTransitionRule :: Prim -> ProofState -> [(ProofState, Seq (Goal.Rule Goal))]
runTransitionRule prim state =
    (runIdentity . unAllPathIdentity . runTransitionT) (transitionRule prim state)

newtype AllPathIdentity a = AllPathIdentity { unAllPathIdentity :: Identity a }
    deriving (Functor, Applicative, Monad)

instance WithLog LogMessage AllPathIdentity where
    askLogAction = undefined
    localLogAction _ = undefined

instance MonadSMT AllPathIdentity where
    withSolver = undefined
    declare = undefined
    declareFun = undefined
    declareSort = undefined
    declareDatatype = undefined
    declareDatatypes = undefined
    assert = undefined
    check = undefined
    ackCommand = undefined
    loadFile = undefined

instance MonadProfiler AllPathIdentity where
    profileDuration _ = id
    profileConfiguration =
        return Configuration
            { identifierFilter = Nothing
            , dumpIdentifier = Nothing
            }

instance MonadSimplify AllPathIdentity where
    askMetadataTools = undefined
    askSimplifierTermLike = undefined
    localSimplifierTermLike = undefined
    askSimplifierPredicate = undefined
    localSimplifierPredicate = undefined
    askSimplifierAxioms = undefined
    localSimplifierAxioms = undefined
    simplifierMemo = undefined
    simplifierRecall = undefined

-- | 'Goal.transitionRule' instantiated with our unit test rules.
transitionRule
    :: Prim
    -> ProofState
    -> Strategy.TransitionT (Goal.Rule Goal) AllPathIdentity ProofState
transitionRule =
    Goal.transitionRule

differentLengthPaths :: [Goal.Rule Goal]
differentLengthPaths =
    fmap Rule
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
