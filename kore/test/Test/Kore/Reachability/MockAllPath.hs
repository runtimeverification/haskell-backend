module Test.Kore.Reachability.MockAllPath (
    test_unprovenNodes,
    test_transitionRule_Begin,
    test_transitionRule_CheckImplication,
    test_transitionRule_ApplyClaims,
    test_transitionRule_ApplyAxioms,
    test_runStrategy,
) where

import Data.Graph.Inductive qualified as Gr
import Data.Limit (
    Limit (..),
 )
import Data.Sequence (
    Seq,
 )
import Data.Sequence qualified as Seq
import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Debug
import Kore.Internal.MultiOr qualified as MultiOr
import Kore.Reachability.Claim (
    AppliedRule (..),
    ApplyResult (..),
    Claim (..),
 )
import Kore.Reachability.Claim qualified as Claim
import Kore.Reachability.ClaimState qualified as ClaimState
import Kore.Reachability.Prim qualified as Prim
import Kore.Rewrite.Strategy qualified as Strategy
import Kore.Rewrite.Transition (
    runTransitionT,
 )
import Kore.Rewrite.Transition qualified as Transition
import Kore.TopBottom (
    TopBottom (..),
 )
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import Test.Kore.Rewrite.MockSymbols qualified as Mock (env)
import Test.Kore.Simplify (testRunSimplifier)
import Test.Tasty
import Test.Tasty.HUnit.Ext
import Test.Terse

newtype MockInteger = MockInteger {unMockInteger :: Integer}
    deriving stock (Eq, Ord)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
    deriving newtype (Num)

instance TopBottom MockInteger where
    isTop _ = False
    isBottom _ = False

--
-- -- * Tests
--
test_unprovenNodes :: [TestTree]
test_unprovenNodes =
    [ unprovenNodes
        (emptyExecutionGraph ClaimState.Proven)
        `satisfies_` null
    , unprovenNodes
        (goal 0)
        `satisfies_` (not . null)
    , unprovenNodes
        (goal 0)
        `equals` [0]
        $ "returns single unproven node"
    , unprovenNodes
        ( goal 0
            & insNode (1, ClaimState.Claimed 1)
            & insNode (2, ClaimState.Proven)
        )
        `equals_` [0, 1]
    , unprovenNodes
        ( goal 0
            & subgoal 0 (1, ClaimState.Claimed 1)
            & subgoal 0 (2, ClaimState.Proven)
        )
        `equals_` [1]
    , unprovenNodes
        ( goal 0
            & subgoal 0 (1, ClaimState.Claimed 1)
            & subgoal 1 (2, ClaimState.Claimed 2)
            & subgoal 2 (3, ClaimState.Proven)
        )
        `equals_` []
    , unprovenNodes
        ( goal 0
            & subgoal 0 (1, ClaimState.Remaining 1)
            & subgoal 0 (2, ClaimState.Proven)
        )
        `equals_` [1]
    ]
  where
    goal :: MockInteger -> ExecutionGraph
    goal n = emptyExecutionGraph (ClaimState.Claimed n)

    subgoal ::
        Gr.Node ->
        (Gr.Node, ClaimState.ClaimState MockInteger) ->
        ExecutionGraph ->
        ExecutionGraph
    subgoal parent node@(child, _) =
        insEdge (parent, child) . insNode node

test_transitionRule_Begin :: [TestTree]
test_transitionRule_Begin =
    [ done ClaimState.Proven
    , unmodifiedAB run (ClaimState.Claimed (MockClaim (A, B)))
    , unmodifiedAB run (ClaimState.Remaining (MockClaim (A, B)))
    ]
  where
    run _ = runTransitionRule [] [] Prim.Begin
    done :: MockClaimState -> TestTree
    done state =
        testCase "null when done" $ run [] state >>= assertBool "" . null

test_transitionRule_CheckImplication :: [TestTree]
test_transitionRule_CheckImplication =
    [ unmodifiedAB run ClaimState.Proven
    , unmodifiedAB run (ClaimState.Stuck (MockClaim (A, B)))
    , ClaimState.Claimed (MockClaim (B, B))
        `becomes` (ClaimState.Proven, mempty)
    ]
  where
    run _rs = runTransitionRule [] [] Prim.CheckImplication
    initial `becomes` final =
        testCase "becomes" $
            run [] initial >>= assertEqual "" [final]

test_transitionRule_ApplyClaims :: [TestTree]
test_transitionRule_ApplyClaims =
    [ unmodifiedAB run ClaimState.Proven
    , unmodifiedAB run (ClaimState.Rewritten (MockClaim (A, B)))
    , [Rule (A, C)]
        `derives` [ (,)
                        (ClaimState.Rewritten (MockClaim (C, C)))
                        (Seq.singleton $ AppliedClaim (MockClaim (A, C)))
                  , (ClaimState.Remaining (MockClaim (Bot, C)), mempty)
                  ]
    , fmap Rule [(A, B), (B, C)]
        `derives` [ (,)
                        (ClaimState.Rewritten (MockClaim (B, C)))
                        (Seq.singleton $ AppliedClaim (MockClaim (A, B)))
                  , (ClaimState.Remaining (MockClaim (Bot, C)), mempty)
                  ]
    ]
  where
    run rules =
        runTransitionRule (map (MockClaim . unRule) rules) [] Prim.ApplyClaims
    derives = derivesFrom run $ ClaimState.Claimed (MockClaim (A, C))

test_transitionRule_ApplyAxioms :: [TestTree]
test_transitionRule_ApplyAxioms =
    [ unmodifiedAB run ClaimState.Proven
    , unmodifiedAB run (ClaimState.Rewritten (MockClaim (A, B)))
    , [Rule (A, C)]
        `derives` [ (,)
                        (ClaimState.Rewritten (MockClaim (C, C)))
                        (Seq.singleton $ axiom (A, C))
                  , (ClaimState.Remaining (MockClaim (Bot, C)), mempty)
                  ]
    , fmap Rule [(A, B), (B, C)]
        `derives` [ (,)
                        (ClaimState.Rewritten (MockClaim (B, C)))
                        (Seq.singleton $ axiom (A, B))
                  , (ClaimState.Remaining (MockClaim (Bot, C)), mempty)
                  ]
    ]
  where
    run rules = runTransitionRule [] [rules] Prim.ApplyAxioms
    axiom = AppliedAxiom . Rule
    derives = derivesFrom run $ ClaimState.Remaining (MockClaim (A, C))

unmodifiedAB ::
    (Diff a, Diff b, Debug a, Debug b, Monoid b) =>
    ([Rule MockClaim] -> a -> IO [(a, b)]) ->
    a ->
    TestTree
unmodifiedAB run state =
    testCase "unmodified" $
        run [Rule (A, B)] state >>= assertEqual "" [(state, mempty)]

derivesFrom ::
    HasCallStack =>
    ([MockRule] -> MockClaimState -> IO [(MockClaimState, Seq MockAppliedRule)]) ->
    -- start state
    MockClaimState ->
    -- rules to apply in parallel
    [MockRule] ->
    -- transitions
    [(MockClaimState, Seq MockAppliedRule)] ->
    TestTree
derivesFrom run state rules result =
    testCase "derives" $
        run rules state >>= assertEqual "" result

test_runStrategy :: [TestTree]
test_runStrategy =
    [ [] `proves` MockClaim (A, A)
    , [] `disproves` MockClaim (A, B) $ [MockClaim (A, B)]
    , [Rule (A, Bot)] `proves` MockClaim (A, A)
    , [Rule (A, Bot)] `proves` MockClaim (A, B)
    , [Rule (A, B)] `proves` MockClaim (A, B)
    , [Rule (A, B)] `proves` MockClaim (A, BorC)
    , [Rule (A, B)] `disproves` MockClaim (A, C) $ [MockClaim (B, C)]
    , [Rule (A, A)] `proves` MockClaim (A, B)
    , [Rule (A, A)] `proves` MockClaim (A, C)
    , [Rule (A, NotDef)] `disproves` MockClaim (A, C) $ []
    , fmap Rule [(A, B), (A, C)] `proves` MockClaim (A, BorC)
    , fmap Rule [(A, B), (A, C)]
        `disproves` MockClaim (A, B)
        $ [MockClaim (C, B)]
    , differentLengthPaths `proves` MockClaim (A, F)
    ]
  where
    run ::
        [MockRule] ->
        MockRule ->
        IO (Strategy.ExecutionGraph MockClaimState MockAppliedRule)
    run axioms goal =
        testRunSimplifier Mock.env $
            Strategy.runStrategy
                Unlimited
                (Claim.transitionRule Claim.EnabledStuckCheck [MockClaim (unRule goal)] [axioms])
                (toList Claim.strategy)
                (ClaimState.Claimed . MockClaim . unRule $ goal)
    disproves ::
        HasCallStack =>
        -- Axioms
        [MockRule] ->
        -- Proof goal
        MockClaim ->
        -- Unproven goals
        [MockClaim] ->
        TestTree
    disproves axioms (MockClaim goal) unproven =
        testCase (show axioms ++ " disproves " ++ show goal) $
            run axioms (Rule goal) >>= assertEqual "" unproven . unprovenNodes

    proves ::
        HasCallStack =>
        -- Axioms
        [MockRule] ->
        -- Proof goal
        MockClaim ->
        TestTree
    proves axioms (MockClaim goal) =
        testCase (show axioms ++ " proves " ++ show goal) $
            run axioms (Rule goal) >>= assertBool "" . proven

-- * Definitions

type ExecutionGraph =
    Strategy.ExecutionGraph
        (ClaimState.ClaimState MockInteger)
        MockAppliedRule

emptyExecutionGraph :: ClaimState.ClaimState MockInteger -> ExecutionGraph
emptyExecutionGraph = Strategy.emptyExecutionGraph

insNode ::
    (Gr.Node, ClaimState.ClaimState MockInteger) ->
    ExecutionGraph ->
    ExecutionGraph
insNode = Strategy.insNode

insEdge ::
    (Gr.Node, Gr.Node) ->
    ExecutionGraph ->
    ExecutionGraph
insEdge = Strategy.insEdge

-- | Simple program configurations for unit testing.
data K = BorC | A | B | C | D | E | F | NotDef | Bot
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance TopBottom K where
    isTop _ = False

    isBottom Bot = True
    isBottom _ = False

instance Pretty K where
    pretty = pretty . show

matches :: K -> K -> Bool
matches B BorC = True
matches C BorC = True
matches a b = a == b

difference :: K -> K -> K
difference BorC B = C
difference BorC C = B
difference a b
    | a `matches` b = Bot
    | otherwise = a

newtype MockClaim = MockClaim {unMockClaim :: (K, K)}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance TopBottom MockClaim where
    isTop _ = False
    isBottom _ = False

type Prim = Claim.Prim

type MockAppliedRule = Claim.AppliedRule MockClaim

type MockRule = Claim.Rule MockClaim

type MockClaimState = ClaimState.ClaimState MockClaim

instance Claim MockClaim where
    newtype Rule MockClaim = Rule {unRule :: (K, K)}
        deriving stock (Eq, Show)
        deriving stock (GHC.Generic)
        deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
        deriving anyclass (Debug, Diff)

    checkImplication claim@(MockClaim (src, dst))
        | src' == Bot = return $ Claim.Implied claim
        | src == NotDef = return $ Claim.Implied claim
        | otherwise = return $ Claim.NotImplied (MockClaim (src', dst))
      where
        src' = difference src dst

    simplify = return

    applyClaims claims =
        derivePar AppliedClaim (map (Rule . unMockClaim) claims)

    applyAxioms axiomGroups =
        derivePar (AppliedAxiom . Rule . unMockClaim) (concat axiomGroups)

derivePar ::
    (MockClaim -> MockAppliedRule) ->
    [MockRule] ->
    MockClaim ->
    Transition.TransitionT MockAppliedRule m (ApplyResult MockClaim)
derivePar mkAppliedRule rules (MockClaim (src, dst)) =
    goals <|> goalRemainder
  where
    goal (Rule rule@(_, to)) = do
        Transition.addRule (mkAppliedRule (MockClaim rule))
        (pure . ApplyRewritten . MockClaim) (to, dst)
    goalRemainder = do
        let r = foldl' difference src (fst . unRule <$> applied)
        (pure . ApplyRemainder . MockClaim) (r, dst)
    applyRule rule@(Rule (fromMockClaim, _))
        | fromMockClaim `matches` src = Just rule
        | otherwise = Nothing
    applied = mapMaybe applyRule rules
    goals = asum (goal <$> applied)

runTransitionRule ::
    [MockClaim] ->
    [[MockRule]] ->
    Prim ->
    MockClaimState ->
    IO [(MockClaimState, Seq MockAppliedRule)]
runTransitionRule claims axiomGroups prim state =
    (testRunSimplifier Mock.env . runTransitionT)
        (Claim.transitionRule Claim.EnabledStuckCheck claims axiomGroups prim state)

differentLengthPaths :: [MockRule]
differentLengthPaths =
    fmap
        Rule
        [ -- Length 5 path
          (A, B)
        , (B, C)
        , (C, D)
        , (D, E)
        , (E, F)
        , -- Length 4 path
          (D, F)
        , -- Length 3 path
          (C, F)
        , -- Length 2 path
          (B, F)
        , -- Length 1 path
          (A, F)
        ]

{- | The final nodes of an execution graph which were not proven.

See also: 'Strategy.pickFinal', 'extractUnproven'
-}
unprovenNodes ::
    forall a.
    (Ord a, TopBottom a) =>
    Strategy.ExecutionGraph (ClaimState.ClaimState a) (AppliedRule MockClaim) ->
    [a]
unprovenNodes executionGraph =
    toList . MultiOr.make $
        mapMaybe ClaimState.extractUnproven $
            Strategy.pickFinal executionGraph

-- | Does the 'Strategy.ExecutionGraph' indicate a successful proof?
proven ::
    forall a.
    (Ord a, TopBottom a) =>
    Strategy.ExecutionGraph (ClaimState.ClaimState a) (AppliedRule MockClaim) ->
    Bool
proven = null . unprovenNodes
