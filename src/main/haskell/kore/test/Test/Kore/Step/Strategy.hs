module Test.Kore.Step.Strategy where

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.QuickCheck

import Data.Functor.Identity
import Numeric.Natural
import Prelude hiding
       ( and, or )

import           Kore.Step.Strategy
                 ( Limit (..), Strategy, Tree (..) )
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

apply :: Prim -> Strategy Prim -> Strategy Prim
apply = Strategy.apply

and :: Strategy Prim -> Strategy Prim -> Strategy Prim
and = Strategy.and

or :: Strategy Prim -> Strategy Prim -> Strategy Prim
or = Strategy.or

many :: (Strategy Prim -> Strategy Prim) -> Strategy Prim -> Strategy Prim
many = Strategy.many

step :: Strategy Prim -> Strategy Prim
step = Strategy.step

stuck :: Strategy Prim
stuck = Strategy.stuck

throw :: Strategy Prim -> Strategy Prim
throw = apply Throw

runStrategy
    :: Strategy Prim
    -> Limit Natural
    -> Natural
    -> Tree (Strategy Prim, Natural)
runStrategy strategy stepLimit z =
    let
        Identity rs = Strategy.runStrategy transitionPrim strategy stepLimit z
    in
        rs

test_And :: [TestTree]
test_And =
    [
        let
            expect =
                Node (s0, 0)
                    [ Node (s1, 0) []
                    , Node (s2, 0)
                        [ Node (s3, 1) [] ]
                    ]
            s0 = and s1 s2
            s1 = stuck
            s2 = apply (Const 1) s3
            s3 = stuck
            actual = runStrategy s0 Unlimited 0
        in
            testCase "Stuck on left" (expect @=? actual)
    ,
        let
            expect =
                Node (s0, 0)
                    [ Node (s1, 0)
                        [ Node (s3, 1) [] ]
                    , Node (s2, 0) []
                    ]
            s0 = and s1 s2
            s1 = apply (Const 1) s3
            s2 = stuck
            s3 = stuck
            actual = runStrategy s0 Unlimited 0
        in
            testCase "Stuck on right" (expect @=? actual)
    ]

test_Or :: [TestTree]
test_Or =
    [
        let
            expect =
                Node (s0, 0)
                    [ Node (s1, 0)
                        [ Node (or s2 stuck, 0)
                            [ Node (s2, 0)
                                [ Node (s3, 1) [] ]
                            ]
                        ]
                    ]
            s0 = or s1 s2
            s1 = throw stuck
            s2 = apply (Const 1) s3
            s3 = stuck
            actual = runStrategy s0 Unlimited 0
        in
            testCase "Throw on left" (expect @=? actual)
    ,
        let
            expect =
                Node (s0, 0)
                    [ Node (s1, 0)
                        [ Node (s3, 1) [] ]
                    ]
            s0 = or s1 s2
            s1 = apply (Const 1) s3
            s2 = throw stuck
            s3 = stuck
            actual = runStrategy s0 Unlimited 0
        in
            testCase "Throw on right" (expect @=? actual)
    ]

prop_stepLimit :: Integer -> Property
prop_stepLimit i =
    (i >= 0) ==> (expect === actual)
  where
    n = fromInteger i
    level m = singleton . Node m
    [expect] = foldr (\m -> level m . level m . level m) [] [0..n]
    actual = snd <$> enumerate n
    singleton x = [x]

enumStrategy :: (Strategy Prim -> Strategy Prim) -> Strategy Prim -> Strategy Prim
enumStrategy each = step . each . apply Succ

-- | Enumerate values from zero to @n@, then get stuck.
enumerate
    :: Natural  -- ^ @n@
    -> Tree (Strategy Prim, Natural)
enumerate n = runStrategy (many (enumStrategy id) stuck) (Limit n) 0

prop_pickLongest :: Integer -> Property
prop_pickLongest i =
    (i >= 0) ==> (expect === actual)
  where
    n = fromInteger i
    expect = n
    actual = Strategy.pickLongest (enumerate n)

prop_pickOne :: Integer -> Property
prop_pickOne i =
    (i > 0) ==> (expect === actual)
  where
    n = fromInteger i
    expect = [1]
    actual = Strategy.pickOne (enumerate n)

prop_pickStar :: Integer -> Property
prop_pickStar i =
    (i > 0) ==> (expect === actual)
  where
    n = fromInteger i
    expect = [0..n]
    actual = Strategy.pickStar (enumerate n)

prop_pickPlus :: Integer -> Property
prop_pickPlus i =
    (i > 0) ==> (expect === actual)
  where
    n = fromInteger i
    expect = [1..n]
    actual = Strategy.pickPlus (enumerate n)

-- | Enumerate values from zero to @n@, getting stuck after every result.
enumerate'
    :: Natural  -- ^ @n@
    -> Tree (Strategy Prim, Natural)
enumerate' n = runStrategy (many (enumStrategy $ and stuck) stuck) (Limit n) 0

prop_pickFinal :: Integer -> Property
prop_pickFinal i =
    (i >= 0) ==> (expect === actual)
  where
    n = fromInteger i
    expect = [0..n]
    actual = Strategy.pickFinal (enumerate' n)

