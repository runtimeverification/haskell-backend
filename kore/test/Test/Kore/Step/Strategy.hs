{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Test.Kore.Step.Strategy where

import Test.QuickCheck.Instances ()
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import           Control.Applicative
                 ( Alternative (..) )
import           Data.Functor.Identity
import qualified Data.Graph.Inductive.Graph as Graph
import           Data.Tree
                 ( Tree (..) )
import qualified Data.Tree as Tree
import           Numeric.Natural
import           Prelude hiding
                 ( and, const, or, seq )

import           Data.Limit
                 ( Limit (..) )
import qualified Data.Limit as Limit
import           Data.Maybe
import           Kore.Step.Strategy
                 ( ExecutionGraph (..), Strategy, TransitionT )
import qualified Kore.Step.Strategy as Strategy
import qualified Kore.Step.Transition as Transition

{-| Convert an ExecutionGraph to a Tree, for the sake
of keeping the old Tree-based unit tests.
If the ExecutionGraph has a confluence at any point,
all nodes downstream of it will be duplicated.
From the point of view of these unit tests this behavior is correct.
-}
toTree :: ExecutionGraph config rule -> Tree config
toTree (ExecutionGraph root graph) = Tree.unfoldTree findChildren root
  where
    findChildren node =
        ( fromJust $ Graph.lab graph node
        , map snd $ filter ((node==) . fst) edges)
    edges = map (\(a,b,_) -> (a,b)) $ Graph.labEdges graph

data Prim
    = Const Natural
    | Succ
    | Throw
    deriving (Eq, Ord, Show)

instance Arbitrary Prim where
    arbitrary = do
        c <- Const <$> arbitrary
        elements [c, Succ, Throw]

    shrink = \case
        Const n -> Const <$> shrink n
        Succ -> []
        Throw -> []

instance Arbitrary prim => Arbitrary (Strategy prim) where
    arbitrary = do
        s <- Strategy.seq <$> arbitrary <*> arbitrary
        a <- Strategy.and <$> arbitrary <*> arbitrary
        o <- Strategy.or <$> arbitrary <*> arbitrary
        p <- Strategy.apply <$> arbitrary
        elements [s, a, o, p, Strategy.stuck, Strategy.continue]

    shrink =
        \case
            Strategy.Seq a b ->
                [a, b]
                ++ (Strategy.Seq <$> shrink a <*> pure b)
                ++ (Strategy.Seq <$> pure a <*> shrink b)
            Strategy.And a b ->
                [a, b]
                ++ (Strategy.And <$> shrink a <*> pure b)
                ++ (Strategy.And <$> pure a <*> shrink b)
            Strategy.Or a b ->
                [a, b]
                ++ (Strategy.Or <$> shrink a <*> pure b)
                ++ (Strategy.Or <$> pure a <*> shrink b)
            Strategy.Apply _ -> []
            Strategy.Stuck -> []
            Strategy.Continue -> []

transitionPrim :: Prim -> Natural -> TransitionT Prim Identity Natural
transitionPrim rule n = do
    Transition.addRule rule
    case rule of
        Const i -> pure i
        Succ    -> pure (succ n)
        Throw   -> empty

apply :: Prim -> Strategy Prim
apply = Strategy.apply

seq :: Strategy Prim -> Strategy Prim -> Strategy Prim
seq = Strategy.seq

and :: Strategy Prim -> Strategy Prim -> Strategy Prim
and = Strategy.and

or :: Strategy Prim -> Strategy Prim -> Strategy Prim
or = Strategy.or

many :: Strategy Prim -> Strategy Prim
many = Strategy.many

stuck :: Strategy Prim
stuck = Strategy.stuck

continue :: Strategy Prim
continue = Strategy.continue

throw :: Strategy Prim
throw = apply Throw

const :: Natural -> Strategy Prim
const = apply . Const

succ_ :: Strategy Prim
succ_ = apply Succ

unlimited :: Limit Natural
unlimited = Unlimited

runStrategy
    :: [Strategy Prim]
    -> Natural
    -> ExecutionGraph Natural Prim
runStrategy strategy z =
    let
        Identity rs = Strategy.runStrategy transitionPrim strategy z
    in
        rs

prop_SeqContinueIdentity :: Strategy Prim -> Natural -> Property
prop_SeqContinueIdentity a n =
    let
        expect = runStrategy [a] n
        left = runStrategy [seq continue a] n
        right = runStrategy [seq a continue] n
    in
        (expect === left) .&&. (expect === right)

prop_SeqStuckDominate :: Strategy Prim -> Natural -> Property
prop_SeqStuckDominate a n =
    let
        expect = runStrategy [stuck] n
        left = runStrategy [seq stuck a] n
        right = runStrategy [seq a stuck] n
    in
        (expect === left) .&&. (expect === right)

prop_AndStuckIdentity :: Strategy Prim -> Natural -> Property
prop_AndStuckIdentity a n =
    let
        expect = runStrategy [a] n
        left = runStrategy [and stuck a] n
        right = runStrategy [and a stuck] n
    in
        (expect === left) .&&. (expect === right)

prop_OrStuckIdentity :: Strategy Prim -> Natural -> Property
prop_OrStuckIdentity a n =
    let
        expect = runStrategy [a] n
        left = runStrategy [or stuck a] n
        right = runStrategy [or a stuck] n
    in
        (expect === left) .&&. (expect === right)

prop_Stuck :: Natural -> Property
prop_Stuck n =
    let
        expect = Node n []
        actual = runStrategy [stuck] n
    in
        expect === toTree actual

prop_Continue :: Natural -> Property
prop_Continue n =
    let
        expect = Node n [ Node n [] ]
        actual = runStrategy [continue] n
    in
        expect === toTree actual

test_And :: [TestTree]
test_And =
    [
        let
            expect = Node 0 [ Node 1 [] ]
            strategy = [and stuck (const 1)]
            actual = toTree $ runStrategy strategy 0
        in
            testCase "Stuck on left" (expect @=? actual)
    ,
        let
            expect = Node 0 [ Node 1 [] ]
            strategy = [and (const 1) stuck]
            actual = toTree $ runStrategy strategy 0
        in
            testCase "Stuck on right" (expect @=? actual)
    ]

test_Or :: [TestTree]
test_Or =
    [
        let
            expect = Node 0 [ Node 1 [] ]
            strategy = [or throw (const 1)]
            actual = toTree $ runStrategy strategy 0
        in
            testCase "Throw on left" (expect @=? actual)
    ,
        let
            expect = Node 0 [ Node 1 [] ]
            strategy = [or (const 1) throw]
            actual = toTree $ runStrategy strategy 0
        in
            testCase "Throw on right" (expect @=? actual)
    ]


prop_stepLimit :: Integer -> Property
prop_stepLimit i =
    (i >= 0) ==> (expect === toTree actual)
  where
    n = fromInteger i
    level m = singleton . Node m
    [expect] = foldr level [] [0..n]
    actual = enumerate n
    singleton x = [x]

-- | Enumerate values from zero to @n@, then get stuck.
enumerate
    :: Natural  -- ^ @n@
    -> ExecutionGraph Natural Prim
enumerate n = runStrategy (Limit.replicate (Limit n) succ_) 0

prop_pickLongest :: Integer -> Property
prop_pickLongest i =
    (i >= 0) ==> (expect === actual)
  where
    n = fromInteger i
    expect = n
    actual = Strategy.pickLongest (enumerate n)

prop_pickFinal :: Integer -> Property
prop_pickFinal i =
    (i >= 0) ==> (expect === actual)
  where
    n = fromInteger i
    expect = [n]
    actual = Strategy.pickFinal (enumerate n)

prop_pickOne :: Integer -> Property
prop_pickOne i =
    (i >= 1) ==> (expect == actual)
  where
    n = fromInteger i
    expect = [1]
    actual = Strategy.pickOne (enumerate n)

prop_pickStar :: Integer -> Property
prop_pickStar i =
    (i >= 0) ==> (expect == actual)
  where
    n = fromInteger i
    expect = [0..n]
    actual = Strategy.pickStar (enumerate n)

prop_pickPlus :: Integer -> Property
prop_pickPlus i =
    (i >= 1) ==> (expect == actual)
  where
    n = fromInteger i
    expect = [1..n]
    actual = Strategy.pickPlus (enumerate n)
