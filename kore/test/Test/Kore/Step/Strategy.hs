{-# OPTIONS_GHC -fno-warn-orphans #-}
{-# OPTIONS_GHC -fno-warn-name-shadowing #-}

module Test.Kore.Step.Strategy where

import Test.QuickCheck.Instances ()
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Control.Applicative
    ( Alternative (..)
    )
import Data.Functor.Identity
import qualified Data.Graph.Inductive.Graph as Graph
import qualified Data.Sequence as Seq
import Numeric.Natural
import Prelude hiding
    ( and
    , const
    , or
    , seq
    )

import Data.Limit
    ( Limit (..)
    )
import qualified Data.Limit as Limit
import Kore.Step.Strategy
    ( ExecutionGraph (..)
    , Strategy
    , TransitionT
    )
import qualified Kore.Step.Strategy as Strategy
import qualified Kore.Step.Transition as Transition

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
        expect = Graph.mkGraph [(0, n)] []
        actual = Strategy.graph $ runStrategy [stuck] n
    in
        expect === actual

prop_Continue :: Natural -> Property
prop_Continue n =
    let
        expect =
            Graph.mkGraph
                [ (0, n) , (1, n) ]
                [ (0, 1, Seq.empty) ]
        actual = Strategy.graph $ runStrategy [continue] n
    in
        expect === actual

test_And :: [TestTree]
test_And =
    let
        expect =
            Graph.mkGraph
                [ (0, 0) , (1, 1) ]
                [ (0, 1, Seq.fromList [Const 1]) ]
    in
        [ testCase "Stuck on left" $ do
            let
                strategy = [and stuck (const 1)]
                actual = Strategy.graph $ runStrategy strategy 0
            expect @=? actual
        , testCase "Stuck on right" $ do
            let
                strategy = [and (const 1) stuck]
                actual = Strategy.graph $ runStrategy strategy 0
            expect @=? actual
        ]

test_Or :: [TestTree]
test_Or =
    let
        expect =
            Graph.mkGraph
                [ (0, 0) , (1, 1) ]
                [ (0, 1, Seq.fromList [Const 1]) ]
    in
        [ testCase "Throw on left" $ do
            let
                strategy = [or throw (const 1)]
                actual = Strategy.graph $ runStrategy strategy 0
            expect @=? actual
        , testCase "Throw on right" $ do
            let
                strategy = [or (const 1) throw]
                actual = Strategy.graph $ runStrategy strategy 0
            expect @=? actual
        ]


prop_stepLimit :: Integer -> Property
prop_stepLimit i =
    (i >= 0) ==> (expect === actual)
  where
    n = fromInteger i
    expect =
        Graph.mkGraph nodes edges
      where
        nodes = do
            j <- [0..n]
            return (fromIntegral j, j)
        edges = do
            (j, _) <- init nodes
            return (j, j + 1, Seq.singleton Succ)
    actual = Strategy.graph $ enumerate n

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
