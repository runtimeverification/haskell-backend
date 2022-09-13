{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.Kore.Rewrite.Strategy (
    prop_depthLimit,
    prop_pickLongest,
    prop_pickFinal,
    prop_pickOne,
    prop_pickStar,
    prop_pickPlus,
) where

import Control.Exception qualified as Exception
import Control.Monad.Catch.Pure (
    Catch,
    runCatch,
 )
import Data.Graph.Inductive.Graph qualified as Graph
import Data.Limit (
    Limit (..),
 )
import Data.Limit qualified as Limit
import Data.Sequence qualified as Seq
import Kore.Rewrite.Strategy (
    ExecutionGraph (..),
    TransitionT,
 )
import Kore.Rewrite.Strategy qualified as Strategy
import Kore.Rewrite.Transition qualified as Transition
import Numeric.Natural
import Prelude.Kore hiding (
    and,
    const,
    or,
    seq,
 )
import Test.QuickCheck.Instances ()
import Test.Tasty.QuickCheck

data Prim
    = Const Natural
    | Succ
    | Throw
    deriving stock (Eq, Ord, Show)

instance Arbitrary Prim where
    arbitrary = do
        c <- Const <$> arbitrary
        elements [c, Succ, Throw]

    shrink = \case
        Const n -> Const <$> shrink n
        Succ -> []
        Throw -> []

transitionPrim :: Prim -> Natural -> TransitionT Prim Catch Natural
transitionPrim rule n = do
    Transition.addRule rule
    case rule of
        Const i -> pure i
        Succ -> pure (succ n)
        Throw -> empty

runStrategy ::
    [[Prim]] ->
    Natural ->
    ExecutionGraph Natural Prim
runStrategy strategy z =
    Strategy.runStrategy Unlimited transitionPrim strategy z
        & runCatch
        & either Exception.throw id

prop_depthLimit :: Integer -> Property
prop_depthLimit i =
    (i >= 0) ==> (expect === actual)
  where
    ~n = fromInteger i
    ~expect =
        Graph.mkGraph nodes edges
      where
        ~nodes = do
            j <- [0 .. n]
            return (fromIntegral j, j)
        edges = do
            (j, _) <- init nodes
            return (j, j + 1, Seq.singleton Succ)
    ~actual = Strategy.graph $ enumerate n

-- | Enumerate values from zero to @n@, then get stuck.
enumerate ::
    -- | @n@
    Natural ->
    ExecutionGraph Natural Prim
enumerate n = runStrategy (Limit.replicate (Limit n) [Succ]) 0

prop_pickLongest :: Integer -> Property
prop_pickLongest i =
    (i >= 0) ==> (expect === actual)
  where
    ~n = fromInteger i
    ~expect = n
    ~actual = Strategy.pickLongest (enumerate n)

prop_pickFinal :: Integer -> Property
prop_pickFinal i =
    (i >= 0) ==> (expect === actual)
  where
    ~n = fromInteger i
    ~expect = [n]
    ~actual = Strategy.pickFinal (enumerate n)

prop_pickOne :: Integer -> Property
prop_pickOne i =
    (i >= 1) ==> (expect == actual)
  where
    ~n = fromInteger i
    expect = [1]
    ~actual = Strategy.pickOne (enumerate n)

prop_pickStar :: Integer -> Property
prop_pickStar i =
    (i >= 0) ==> (expect == actual)
  where
    ~n = fromInteger i
    ~expect = [0 .. n]
    ~actual = Strategy.pickStar (enumerate n)

prop_pickPlus :: Integer -> Property
prop_pickPlus i =
    (i >= 1) ==> (expect == actual)
  where
    ~n = fromInteger i
    ~expect = [1 .. n]
    ~actual = Strategy.pickPlus (enumerate n)
