module Test.Kore.Step.Strategy where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Data.Functor.Identity
import Numeric.Natural
import Prelude hiding
       ( and, const, or )

import           Data.Limit
                 ( Limit (..) )
import qualified Data.Limit as Limit
import           Kore.Step.Strategy
                 ( Strategy, Tree (..) )
import qualified Kore.Step.Strategy as Strategy

data Prim
    = Const Natural
    | Succ
    | Throw
    deriving (Eq, Show)

transitionPrim :: Prim -> Natural -> Identity [Natural]
transitionPrim =
    \case
        Const n -> \_ -> pure [n]
        Succ -> \n -> pure [succ n]
        Throw -> \_ -> pure []

apply :: Prim -> Strategy Prim
apply = Strategy.apply

and :: Strategy Prim -> Strategy Prim -> Strategy Prim
and = Strategy.and

or :: Strategy Prim -> Strategy Prim -> Strategy Prim
or = Strategy.or

many :: Strategy Prim -> Strategy Prim
many = Strategy.many

stuck :: Strategy Prim
stuck = Strategy.stuck

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
    -> Tree Natural
runStrategy strategy z =
    let
        Identity rs = Strategy.runStrategy transitionPrim strategy z
    in
        rs

test_And :: [TestTree]
test_And =
    [
        let
            expect = Node 0 [ Node 1 [] ]
            strategy = [and stuck (const 1)]
            actual = runStrategy strategy 0
        in
            testCase "Stuck on left" (expect @=? actual)
    ,
        let
            expect = Node 0 [ Node 1 [] ]
            strategy = [and (const 1) stuck]
            actual = runStrategy strategy 0
        in
            testCase "Stuck on right" (expect @=? actual)
    ]

test_Or :: [TestTree]
test_Or =
    [
        let
            expect = Node 0 [ Node 1 [] ]
            strategy = [or throw (const 1)]
            actual = runStrategy strategy 0
        in
            testCase "Throw on left" (expect @=? actual)
    ,
        let
            expect = Node 0 [ Node 1 [] ]
            strategy = [or (const 1) throw]
            actual = runStrategy strategy 0
        in
            testCase "Throw on right" (expect @=? actual)
    ]

prop_stepLimit :: Integer -> Property
prop_stepLimit i =
    (i >= 0) ==> (expect === actual)
  where
    n = fromInteger i
    level m = singleton . Node m
    [expect] = foldr level [] [0..n]
    actual = enumerate n
    singleton x = [x]

-- | Enumerate values from zero to @n@, then get stuck.
enumerate
    :: Natural  -- ^ @n@
    -> Tree Natural
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
