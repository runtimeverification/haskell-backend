{-# OPTIONS_GHC -fno-warn-name-shadowing #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.Kore.Rewrite.Strategy (
    prop_SeqContinueIdentity,
    prop_Continue,
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
    Strategy,
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

instance Arbitrary prim => Arbitrary (Strategy prim) where
    arbitrary = do
        ~s <- Strategy.seq <$> arbitrary <*> arbitrary
        ~p <- Strategy.apply <$> arbitrary
        elements [s, p, Strategy.continue]

    shrink =
        \case
            Strategy.Seq a b ->
                [a, b]
                    ++ (Strategy.Seq <$> shrink a <*> pure b)
                    ++ (Strategy.Seq a <$> shrink b)
            Strategy.Apply _ -> []
            Strategy.Continue -> []

transitionPrim :: Prim -> Natural -> TransitionT Prim Catch Natural
transitionPrim rule n = do
    Transition.addRule rule
    case rule of
        Const i -> pure i
        Succ -> pure (succ n)
        Throw -> empty

apply :: Prim -> Strategy Prim
apply = Strategy.apply

seq :: Strategy Prim -> Strategy Prim -> Strategy Prim
seq = Strategy.seq

continue :: Strategy Prim
continue = Strategy.continue

succ_ :: Strategy Prim
succ_ = apply Succ

runStrategy ::
    [Strategy Prim] ->
    Natural ->
    ExecutionGraph Natural Prim
runStrategy strategy z =
    Strategy.runStrategy Unlimited transitionPrim strategy z
        & runCatch
        & either Exception.throw id

prop_SeqContinueIdentity :: Strategy Prim -> Natural -> Property
prop_SeqContinueIdentity a n =
    let expect = runStrategy [a] n
        left = runStrategy [seq continue a] n
        right = runStrategy [seq a continue] n
     in (expect === left) .&&. (expect === right)

prop_Continue :: Natural -> Property
prop_Continue n =
    let expect =
            Graph.mkGraph
                [(0, n), (1, n)]
                [(0, 1, Seq.empty)]
        actual = Strategy.graph $ runStrategy [continue] n
     in expect === actual

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
enumerate n = runStrategy (Limit.replicate (Limit n) succ_) 0

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
