module Test.Kore.Strategies.AllPath.AllPath
    ( test_unprovenNodes
    , test_transitionRule_Begin
    , test_transitionRule_CheckImplication
    , test_transitionRule_ApplyClaims
    , test_transitionRule_ApplyAxioms
    , test_runStrategy
    ) where

import Prelude.Kore

import Test.Tasty

import Control.Monad.Catch
    ( MonadCatch (catch)
    , MonadThrow (throwM)
    )
import qualified Data.Foldable as Foldable
import Data.Functor.Identity
import qualified Data.Graph.Inductive as Gr
import Data.Limit
    ( Limit (..)
    )
import Data.Sequence
    ( Seq
    )
import qualified Data.Sequence as Seq
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
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
import Kore.TopBottom
    ( TopBottom (..)
    )
import Log
    ( MonadLog (..)
    )
import Pretty
    ( Pretty (..)
    )
import SMT
    ( MonadSMT (..)
    )

import Test.Terse

newtype MockInteger = MockInteger { unMockInteger :: Integer }
    deriving (Eq, Ord, Num, GHC.Generic)

instance Diff MockInteger
instance SOP.Generic MockInteger
instance SOP.HasDatatypeInfo MockInteger
instance Debug MockInteger

instance TopBottom MockInteger where
    isTop _ = False
    isBottom _ = False

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
    , (Foldable.toList . Goal.unprovenNodes)
        (goal 0)
        `equals`
        [0]
        $  "returns single unproven node"
    , (Foldable.toList . Goal.unprovenNodes)
        (goal 0
            & insNode (1, ProofState.Goal 1)
            & insNode (2, ProofState.Proven)
        )
        `equals_`
        [0, 1]
    , (Foldable.toList . Goal.unprovenNodes)
        (goal 0
            & subgoal 0 (1, ProofState.Goal 1)
            & subgoal 0 (2, ProofState.Proven)
        )
        `equals_`
        [1]
    , (Foldable.toList . Goal.unprovenNodes)
        (goal 0
            & subgoal 0 (1, ProofState.Goal 1)
            & subgoal 1 (2, ProofState.Goal 2)
            & subgoal 2 (3, ProofState.Proven)
        )
        `equals_`
        []
    , (Foldable.toList . Goal.unprovenNodes)
        (goal 0
            & subgoal 0 (1, ProofState.GoalRemainder 1)
            & subgoal 0 (2, ProofState.Proven)
        )
        `equals_`
        [1]
    ]
  where
    goal :: MockInteger -> ExecutionGraph
    goal n = emptyExecutionGraph (ProofState.Goal n)

    subgoal
        :: Gr.Node
        -> (Gr.Node, ProofState.ProofState MockInteger)
        -> ExecutionGraph -> ExecutionGraph
    subgoal parent node@(child, _) =
        insEdge (parent, child) . insNode node

test_transitionRule_Begin :: [TestTree]
test_transitionRule_Begin =
    [ done ProofState.Proven
    , unmodified (ProofState.Goal (Goal (A, B)))
    , unmodified (ProofState.GoalRemainder (Goal (A, B)))
    ]
  where
    run = runTransitionRule [] [] ProofState.Begin
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    done :: HasCallStack => ProofState -> TestTree
    done state = run state `satisfies_` Foldable.null

test_transitionRule_CheckImplication :: [TestTree]
test_transitionRule_CheckImplication =
    [ unmodified ProofState.Proven
    , unmodified (ProofState.GoalStuck (Goal (A, B)))
    , ProofState.Goal (Goal (B, B)) `becomes` (ProofState.Proven, mempty)
    ]
  where
    run = runTransitionRule [] [] ProofState.CheckImplication
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    becomes initial final = run initial `equals_` [final]

test_transitionRule_ApplyClaims :: [TestTree]
test_transitionRule_ApplyClaims =
    [ unmodified ProofState.Proven
    , unmodified (ProofState.GoalRewritten (Goal (A, B)))
    , [Rule (A, C)]
        `derives`
        [ (ProofState.GoalRewritten (Goal (C,   C))
            , Seq.singleton $ Goal.AppliedClaim (Goal (A, C))
          )
        , (ProofState.GoalRemainder (Goal (Bot, C)), mempty)
        ]
    , fmap Rule [(A, B), (B, C)]
        `derives`
        [ (ProofState.GoalRewritten (Goal (B  , C))
            , Seq.singleton $ Goal.AppliedClaim (Goal (A, B))
          )
        , (ProofState.GoalRemainder (Goal (Bot, C)), mempty)
        ]
    ]
  where
    run rules = runTransitionRule (map (Goal . unRule) rules) [] ProofState.ApplyClaims
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run [Rule (A, B)] state `equals_` [(state, mempty)]
    derives
        :: HasCallStack
        => [Goal.Rule Goal]
        -- ^ rules to apply in parallel
        -> [(ProofState, Seq (Goal.AppliedRule Goal))]
        -- ^ transitions
        -> TestTree
    derives rules = equals_ (run rules $ ProofState.Goal (Goal (A, C)))

test_transitionRule_ApplyAxioms :: [TestTree]
test_transitionRule_ApplyAxioms =
    [ unmodified ProofState.Proven
    , unmodified (ProofState.GoalRewritten (Goal (A, B)))
    , [Rule (A, C)]
        `derives`
        [ (ProofState.GoalRewritten (Goal (C,   C)), Seq.singleton $ axiom (A, C))
        , (ProofState.GoalRemainder (Goal (Bot, C)), mempty)
        ]
    , fmap Rule [(A, B), (B, C)]
        `derives`
        [ (ProofState.GoalRewritten (Goal (B  , C)), Seq.singleton $ axiom (A, B))
        , (ProofState.GoalRemainder (Goal (Bot, C)), mempty)
        ]
    ]
  where
    run rules = runTransitionRule [] [rules] ProofState.ApplyAxioms
    axiom = Goal.AppliedAxiom . Rule
    unmodified :: HasCallStack => ProofState -> TestTree
    unmodified state = run [Rule (A, B)] state `equals_` [(state, mempty)]
    derives
        :: HasCallStack
        => [Goal.Rule Goal]
        -- ^ rules to apply in parallel
        -> [(ProofState, Seq (Goal.AppliedRule Goal))]
        -- ^ transitions
        -> TestTree
    derives rules = equals_ (run rules $ ProofState.GoalRemainder (Goal (A, C)))

test_runStrategy :: [TestTree]
test_runStrategy =
    [ [] `proves`    Goal (A, A)
    , [] `disproves` Goal (A, B) $ [Goal (A, B)]

    , [Rule (A, Bot)] `proves` Goal (A, A)
    , [Rule (A, Bot)] `proves` Goal (A, B)

    , [Rule (A, B)] `proves`    Goal (A, B   )
    , [Rule (A, B)] `proves`    Goal (A, BorC)
    , [Rule (A, B)] `disproves` Goal (A, C   ) $ [Goal (B, C)]

    , [Rule (A, A)] `proves` Goal (A, B)
    , [Rule (A, A)] `proves` Goal (A, C)

    , [Rule (A, NotDef)] `disproves` Goal (A, C) $ []

    , fmap Rule [(A, B), (A, C)] `proves`    Goal (A, BorC)
    , fmap Rule [(A, B), (A, C)] `disproves` Goal (A, B   ) $ [Goal (C, B)]

    , differentLengthPaths `proves` Goal (A, F)
    ]
  where
    run
        :: [Goal.Rule Goal]
        -> Goal.Rule Goal
        -> Strategy.ExecutionGraph ProofState (Goal.AppliedRule Goal)
    run axioms goal =
        runIdentity
        . unAllPathIdentity
        $ Strategy.runStrategy
            Unlimited
            (Goal.transitionRule [Goal (unRule goal)] [axioms])
            (Foldable.toList Goal.strategy)
            (ProofState.Goal . Goal . unRule $ goal)
    disproves
        :: HasCallStack
        => [Goal.Rule Goal]
        -- ^ Axioms
        -> Goal
        -- ^ Proof goal
        -> [Goal]
        -- ^ Unproven goals
        -> TestTree
    disproves axioms (Goal goal) unproven =
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
    proves axioms (Goal goal) =
        satisfies
            (run axioms (Rule goal))
            Goal.proven
            (show axioms ++ " proves " ++ show goal)

-- * Definitions

type ExecutionGraph =
    Strategy.ExecutionGraph
        (ProofState.ProofState MockInteger)
        (Goal.AppliedRule Goal)

emptyExecutionGraph :: ProofState.ProofState MockInteger -> ExecutionGraph
emptyExecutionGraph = Strategy.emptyExecutionGraph

insNode
    :: (Gr.Node, ProofState.ProofState MockInteger)
    -> ExecutionGraph
    -> ExecutionGraph
insNode = Strategy.insNode

insEdge
    :: (Gr.Node, Gr.Node)
    -> ExecutionGraph
    -> ExecutionGraph
insEdge = Strategy.insEdge

-- | Simple program configurations for unit testing.
data K = BorC | A | B | C | D | E | F | NotDef | Bot
    deriving (Eq, GHC.Generic, Ord, Show)

instance SOP.Generic K

instance SOP.HasDatatypeInfo K

instance Debug K

instance Diff K

instance TopBottom K where
    isTop _ = False

    isBottom Bot = True
    isBottom _ = False

instance Pretty K where
    pretty = pretty . show

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

newtype Goal = Goal { unGoal :: (K, K) }
    deriving (Eq, Ord, GHC.Generic)

instance Diff Goal
instance SOP.Generic Goal
instance SOP.HasDatatypeInfo Goal
instance Debug Goal

instance TopBottom Goal where
    isTop _ = False
    isBottom _ = False

type ProofState = ProofState.ProofState Goal

type Prim = Goal.Prim

newtype instance Goal.Rule Goal =
    Rule { unRule :: (K, K) }
    deriving (Eq, GHC.Generic, Show)

instance Goal.Goal Goal where
    checkImplication (Goal (src, dst))
      | src' == Bot = return Goal.Implied
      | src == NotDef = return Goal.Implied
      | otherwise = return $ Goal.NotImplied (Goal (src', dst))
      where
        src' = difference src dst

    simplify = return

    applyClaims claims =
        derivePar Goal.AppliedClaim (map (Rule . unGoal) claims)

    applyAxioms axiomGroups =
        derivePar (Goal.AppliedAxiom . Rule . unGoal) (concat axiomGroups)

derivePar
    :: (Goal -> Goal.AppliedRule Goal)
    -> [Goal.Rule Goal]
    -> Goal
    -> Transition.TransitionT (Goal.AppliedRule Goal) m (ProofState.ProofState Goal)
derivePar mkAppliedRule rules (Goal (src, dst)) =
    goals <|> goalRemainder
  where
    goal (Rule rule@(_, to)) = do
        Transition.addRule (mkAppliedRule (Goal rule))
        (pure . ProofState.GoalRewritten . Goal) (to, dst)
    goalRemainder = do
        let r = Foldable.foldl' difference src (fst . unRule <$> applied)
        (pure . ProofState.GoalRemainder . Goal) (r, dst)
    applyRule rule@(Rule (fromGoal, _))
        | fromGoal `matches` src = Just rule
        | otherwise = Nothing
    applied = mapMaybe applyRule rules
    goals = Foldable.asum (goal <$> applied)

instance SOP.Generic (Goal.Rule Goal)

instance SOP.HasDatatypeInfo (Goal.Rule Goal)

instance Debug (Goal.Rule Goal)

instance Diff (Goal.Rule Goal)

runTransitionRule
    :: [Goal]
    -> [[Goal.Rule Goal]]
    -> Prim
    -> ProofState
    -> [(ProofState, Seq (Goal.AppliedRule Goal))]
runTransitionRule claims axiomGroups prim state =
    (runIdentity . unAllPathIdentity . runTransitionT)
        (Goal.transitionRule claims axiomGroups prim state)

newtype AllPathIdentity a = AllPathIdentity { unAllPathIdentity :: Identity a }
    deriving (Functor, Applicative, Monad)

instance MonadLog AllPathIdentity where
    logEntry = undefined
    logWhile _ = undefined

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
    reinit = undefined

instance MonadThrow AllPathIdentity where
    throwM _ = error "Unimplemented"

instance MonadCatch AllPathIdentity where
    catch action _handler = action

instance MonadSimplify AllPathIdentity where
    askMetadataTools = undefined
    simplifyTermLike = undefined
    simplifyCondition = undefined
    askSimplifierAxioms = undefined
    localSimplifierAxioms = undefined
    askMemo = undefined
    askInjSimplifier = undefined
    askOverloadSimplifier = undefined

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
