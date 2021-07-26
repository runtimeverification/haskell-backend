module Test.Kore.Reachability.MockAllPath (
    test_unprovenNodes,
    test_transitionRule_Begin,
    test_transitionRule_CheckImplication,
    test_transitionRule_ApplyClaims,
    test_transitionRule_ApplyAxioms,
    test_runStrategy,
) where

import Control.Monad.Catch (
    MonadCatch (catch),
    MonadThrow (throwM),
 )
import Data.Functor.Identity
import qualified Data.Graph.Inductive as Gr
import Data.Limit (
    Limit (..),
 )
import Data.Sequence (
    Seq,
 )
import qualified Data.Sequence as Seq
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Debug
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Reachability.Claim (
    AppliedRule (..),
    ApplyResult (..),
    Claim (..),
 )
import qualified Kore.Reachability.Claim as Claim
import qualified Kore.Reachability.ClaimState as ClaimState
import qualified Kore.Reachability.Prim as Prim
import qualified Kore.Rewrite.Strategy as Strategy
import Kore.Rewrite.Transition (
    runTransitionT,
 )
import qualified Kore.Rewrite.Transition as Transition
import Kore.Simplify.Data (
    MonadSimplify (..),
 )
import Kore.TopBottom (
    TopBottom (..),
 )
import Log (
    MonadLog (..),
 )
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import SMT (
    MonadSMT (..),
 )
import Test.Tasty
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
    , unmodified (ClaimState.Claimed (MockClaim (A, B)))
    , unmodified (ClaimState.Remaining (MockClaim (A, B)))
    ]
  where
    run = runTransitionRule [] [] Prim.Begin
    unmodified :: HasCallStack => MockClaimState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    done :: HasCallStack => MockClaimState -> TestTree
    done state = run state `satisfies_` null

test_transitionRule_CheckImplication :: [TestTree]
test_transitionRule_CheckImplication =
    [ unmodified ClaimState.Proven
    , unmodified (ClaimState.Stuck (MockClaim (A, B)))
    , ClaimState.Claimed (MockClaim (B, B))
        `becomes` (ClaimState.Proven, mempty)
    ]
  where
    run = runTransitionRule [] [] Prim.CheckImplication
    unmodified :: HasCallStack => MockClaimState -> TestTree
    unmodified state = run state `equals_` [(state, mempty)]
    becomes initial final = run initial `equals_` [final]

test_transitionRule_ApplyClaims :: [TestTree]
test_transitionRule_ApplyClaims =
    [ unmodified ClaimState.Proven
    , unmodified (ClaimState.Rewritten (MockClaim (A, B)))
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
    unmodified :: HasCallStack => MockClaimState -> TestTree
    unmodified state = run [Rule (A, B)] state `equals_` [(state, mempty)]
    derives ::
        HasCallStack =>
        -- | rules to apply in parallel
        [MockRule] ->
        -- | transitions
        [(MockClaimState, Seq MockAppliedRule)] ->
        TestTree
    derives rules = equals_ (run rules $ ClaimState.Claimed (MockClaim (A, C)))

test_transitionRule_ApplyAxioms :: [TestTree]
test_transitionRule_ApplyAxioms =
    [ unmodified ClaimState.Proven
    , unmodified (ClaimState.Rewritten (MockClaim (A, B)))
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
    unmodified :: HasCallStack => MockClaimState -> TestTree
    unmodified state = run [Rule (A, B)] state `equals_` [(state, mempty)]
    derives ::
        HasCallStack =>
        -- | rules to apply in parallel
        [MockRule] ->
        -- | transitions
        [(MockClaimState, Seq MockAppliedRule)] ->
        TestTree
    derives rules =
        equals_ (run rules $ ClaimState.Remaining (MockClaim (A, C)))

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
        Strategy.ExecutionGraph MockClaimState MockAppliedRule
    run axioms goal =
        runIdentity
            . unAllPathIdentity
            $ Strategy.runStrategy
                Unlimited
                (Claim.transitionRule [MockClaim (unRule goal)] [axioms])
                (toList Claim.strategy)
                (ClaimState.Claimed . MockClaim . unRule $ goal)
    disproves ::
        HasCallStack =>
        -- | Axioms
        [MockRule] ->
        -- | Proof goal
        MockClaim ->
        -- | Unproven goals
        [MockClaim] ->
        TestTree
    disproves axioms (MockClaim goal) unproven =
        equals
            (unprovenNodes $ run axioms (Rule goal))
            unproven
            (show axioms ++ " disproves " ++ show goal)
    proves ::
        HasCallStack =>
        -- | Axioms
        [MockRule] ->
        -- | Proof goal
        MockClaim ->
        TestTree
    proves axioms (MockClaim goal) =
        satisfies
            (run axioms (Rule goal))
            proven
            (show axioms ++ " proves " ++ show goal)

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
    deriving stock (Eq, Ord)
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

    checkImplication (MockClaim (src, dst))
        | src' == Bot = return Claim.Implied
        | src == NotDef = return Claim.Implied
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
    [(MockClaimState, Seq MockAppliedRule)]
runTransitionRule claims axiomGroups prim state =
    (runIdentity . unAllPathIdentity . runTransitionT)
        (Claim.transitionRule claims axiomGroups prim state)

newtype AllPathIdentity a = AllPathIdentity {unAllPathIdentity :: Identity a}
    deriving newtype (Functor, Applicative, Monad)

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
