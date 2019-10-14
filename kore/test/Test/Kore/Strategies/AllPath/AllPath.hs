module Test.Kore.Strategies.AllPath.AllPath where

import Test.Tasty

import Control.Applicative
import Control.Monad.Catch
    ( MonadCatch (catch)
    , MonadThrow (throwM)
    )
import qualified Data.Foldable as Foldable
import Data.Function
    ( (&)
    )
import Data.Functor.Identity
import qualified Data.Graph.Inductive as Gr
import qualified Data.Maybe as Maybe
import Data.Sequence
    ( Seq
    )
import qualified Data.Sequence as Seq
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import GHC.Stack
    ( HasCallStack
    )

import Kore.Debug
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Logger
    ( LogMessage (..)
    , WithLog (..)
    )
import Kore.Profiler.Data
    ( Configuration (..)
    , Destination (..)
    , MonadProfiler (..)
    )
import Kore.Step.Simplification.Data
    ( MonadSimplify (..)
    )
import qualified Kore.Step.Strategy as Strategy
import Kore.Step.Transition
    ( runTransitionT
    )
import qualified Kore.Step.Transition as Transition
import qualified Kore.Strategies.Goal as Goal
import qualified Kore.Strategies.ProofState as ProofState
import SMT
    ( MonadSMT (..)
    )

import Test.Terse

--
-- -- * Tests
--
test_unprovenNodes :: [TestTree]
test_unprovenNodes =
    [ Goal.unprovenNodes
        (emptyExecutionGraph ProofState.Proven)
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
            & insNode (1, ProofState.Goal 1)
            & insNode (2, ProofState.Proven)
        )
        `equals_`
        MultiOr.MultiOr [0, 1]
    , Goal.unprovenNodes
        (goal 0
            & subgoal 0 (1, ProofState.Goal 1)
            & subgoal 0 (2, ProofState.Proven)
        )
        `equals_`
        MultiOr.MultiOr [1]
    , Goal.unprovenNodes
        (goal 0
            & subgoal 0 (1, ProofState.Goal 1)
            & subgoal 1 (2, ProofState.Goal 2)
            & subgoal 2 (3, ProofState.Proven)
        )
        `equals_`
        MultiOr.MultiOr []
    , Goal.unprovenNodes
        (goal 0
            & subgoal 0 (1, ProofState.GoalRemainder 1)
            & subgoal 0 (2, ProofState.Proven)
        )
        `equals_`
        MultiOr.MultiOr [1]
    ]
  where
    goal :: Integer -> ExecutionGraph
    goal n = emptyExecutionGraph (ProofState.Goal n)

    subgoal
        :: Gr.Node
        -> (Gr.Node, Goal.ProofState Goal Integer)
        -> ExecutionGraph -> ExecutionGraph
    subgoal parent node@(child, _) =
        insEdge (parent, child) . insNode node

test_transitionRule_CheckProven :: [TestTree]
test_transitionRule_CheckProven =
    [ done ProofState.Proven
    , unmodified (ProofState.Goal    (A, B))
    , unmodified (ProofState.GoalRemainder (A, B))
    ]
  where
    run = runTransitionRule ProofState.CheckProven
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    done :: HasCallStack => ProofState -> TestTree
    done state = run state `satisfies_` Foldable.null

test_transitionRule_CheckGoalRem :: [TestTree]
test_transitionRule_CheckGoalRem =
    [ unmodified ProofState.Proven
    , unmodified (ProofState.Goal    (A, B))
    , done       (ProofState.GoalRemainder undefined)
    ]
  where
    run = runTransitionRule ProofState.CheckGoalRemainder
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    done :: HasCallStack => ProofState -> TestTree
    done state = run state `satisfies_` Foldable.null

test_transitionRule_RemoveDestination :: [TestTree]
test_transitionRule_RemoveDestination =
    [ unmodified ProofState.Proven
    , unmodified (ProofState.GoalRemainder (A, B))
    , ProofState.Goal (B, B) `becomes` (ProofState.Goal (Bot, B), mempty)
    ]
  where
    run = runTransitionRule ProofState.RemoveDestination
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    becomes initial final = run initial `equals_` [final]

test_transitionRule_TriviallyValid :: [TestTree]
test_transitionRule_TriviallyValid =
    [ unmodified    ProofState.Proven
    , unmodified    (ProofState.Goal    (A, B))
    , unmodified    (ProofState.GoalRemainder (A, B))
    , becomesProven (ProofState.GoalRemainder (Bot, B))
    ]
  where
    run = runTransitionRule ProofState.TriviallyValid
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    becomesProven :: HasCallStack => ProofState -> TestTree
    becomesProven state = run state `equals_` [(ProofState.Proven, mempty)]

test_transitionRule_DerivePar :: [TestTree]
test_transitionRule_DerivePar =
    [ unmodified ProofState.Proven
    , unmodified (ProofState.GoalRewritten    (A, B))
    , [Rule (A, C)]
        `derives`
        [ (ProofState.Goal    (C,   C), Seq.singleton $ Rule (A, C))
        , (ProofState.GoalRemainder (Bot, C), mempty)
        ]
    , fmap Rule [(A, B), (B, C)]
        `derives`
        [ (ProofState.Goal    (B  , C), Seq.singleton $ Rule (A, B))
        , (ProofState.GoalRemainder (Bot, C), mempty)
        ]
    ]
  where
    run rules = runTransitionRule (ProofState.DerivePar rules)
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run [Rule (A, B)] state `equals_` [(state, mempty)]
    derives
        :: HasCallStack
        => [Goal.Rule Goal]
        -- ^ rules to apply in parallel
        -> [(ProofState, Seq (Goal.Rule Goal))]
        -- ^ transitions
        -> TestTree
    derives rules = equals_ (run rules $ ProofState.GoalRemainder (A, C))

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
            Goal.transitionRule
            (Goal.strategy [unRule goal] axioms)
            (ProofState.Goal . unRule $ goal)
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

type ExecutionGraph = Strategy.ExecutionGraph (Goal.ProofState Goal Integer) (Goal.Rule Goal)

emptyExecutionGraph :: Goal.ProofState Goal Integer -> ExecutionGraph
emptyExecutionGraph = Strategy.emptyExecutionGraph

insNode
    :: (Gr.Node, Goal.ProofState Goal Integer)
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
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic K

instance SOP.HasDatatypeInfo K

instance Debug K

instance Diff K

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

type Goal = (K, K)

type ProofState = Goal.ProofState Goal Goal

type Prim = Goal.Prim Goal

instance Goal.Goal Goal where

    newtype Rule Goal =
        Rule { unRule :: (K, K) }
        deriving (Eq, GHC.Generic, Show)

    type Prim Goal = ProofState.Prim (Goal.Rule Goal)

    type ProofState Goal a = ProofState.ProofState a

    strategy goals rules =
        firstStep : repeat nextStep
      where
        firstStep =
            (Strategy.sequence . map Strategy.apply)
                [ ProofState.CheckProven
                , ProofState.CheckGoalRemainder
                , ProofState.RemoveDestination
                , ProofState.TriviallyValid
                , ProofState.DerivePar axioms
                , ProofState.Simplify
                , ProofState.TriviallyValid
                , ProofState.ResetGoal
                , ProofState.TriviallyValid
                ]
        nextStep =
            (Strategy.sequence . map Strategy.apply)
                [ ProofState.CheckProven
                , ProofState.CheckGoalRemainder
                , ProofState.RemoveDestination
                , ProofState.TriviallyValid
                , ProofState.DeriveSeq claims
                , ProofState.RemoveDestination
                , ProofState.Simplify
                , ProofState.TriviallyValid
                , ProofState.DerivePar axioms
                , ProofState.RemoveDestination
                , ProofState.Simplify
                , ProofState.TriviallyValid
                , ProofState.ResetGoal
                , ProofState.TriviallyValid
                ]
        axioms = rules
        claims = Rule <$> goals

    transitionRule =
        Goal.transitionRuleTemplate
            Goal.TransitionRuleTemplate
                { simplifyTemplate =
                    simplify
                , removeDestinationTemplate =
                    removeDestination
                , isTriviallyValidTemplate =
                    isTriviallyValid
                , deriveParTemplate =
                    derivePar
                , deriveSeqTemplate =
                    deriveSeq
                }

instance SOP.Generic (Goal.Rule Goal)

instance SOP.HasDatatypeInfo (Goal.Rule Goal)

instance Debug (Goal.Rule Goal)

instance Diff (Goal.Rule Goal)

-- | The destination-removal rule for our unit test goal.
removeDestination
    :: MonadSimplify m
    => Goal
    -> Strategy.TransitionT (Goal.Rule Goal) m Goal
removeDestination (src, dst) =
    return (difference src dst, dst)

-- | The goal is trivially valid when the members are equal.
isTriviallyValid :: Goal -> Bool
isTriviallyValid (src, _) = src == Bot

derivePar
    :: MonadSimplify m
    => [Goal.Rule Goal]
    -> Goal
    -> Strategy.TransitionT (Goal.Rule Goal) m ProofState
derivePar rules (src, dst) =
    goals <|> goalRemainder
  where
    goal rule@(Rule (_, to)) = do
        Transition.addRule rule
        (pure . ProofState.Goal) (to, dst)
    goalRemainder = do
        let r = Foldable.foldl' difference src (fst . unRule <$> applied)
        (pure . ProofState.GoalRemainder) (r, dst)
    applyRule rule@(Rule (from, _))
      | from `matches` src = Just rule
      | otherwise = Nothing
    applied = Maybe.mapMaybe applyRule rules
    goals = Foldable.asum (goal <$> applied)

simplify
    :: MonadSimplify m
    => Goal
    -> Strategy.TransitionT (Goal.Rule Goal) m Goal
simplify = return

isTrusted :: Goal -> Bool
isTrusted = undefined

deriveSeq
    :: MonadSimplify m
    => [Goal.Rule Goal]
    -> Goal
    -> Strategy.TransitionT (Goal.Rule Goal) m ProofState
deriveSeq = derivePar

runTransitionRule :: Prim -> ProofState -> [(ProofState, Seq (Goal.Rule Goal))]
runTransitionRule prim state =
    (runIdentity . unAllPathIdentity . runTransitionT)
        (Goal.transitionRule prim state)

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
    profile _ = id
    profileConfiguration =
        return Configuration
            { identifierFilter = Nothing
            , dumpIdentifier = Nothing
            , destination = HumanReadable
            , logBranching = False
            , logStrategy = False
            , logSimplification = False
            , logInitialization = False
            , logEvaluation = False
            , logSmt = False
            }

instance MonadThrow AllPathIdentity where
    throwM _ = error "Unimplemented"

instance MonadCatch AllPathIdentity where
    catch action _handler = action

instance MonadSimplify AllPathIdentity where
    askMetadataTools = undefined
    askSimplifierTermLike = undefined
    localSimplifierTermLike = undefined
    simplifyPredicate = undefined
    askSimplifierAxioms = undefined
    localSimplifierAxioms = undefined
    askMemo = undefined

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
