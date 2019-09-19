module Test.ListT where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.HUnit

import Control.Monad.Reader
    ( Reader
    )
import qualified Control.Monad.Reader as Reader
import qualified Data.Foldable as Foldable
import qualified Data.Function as Function
import Data.Functor.Identity

import ListT

genList :: Gen a -> Gen (ListT Identity a)
genList genItem =
    Foldable.asum . map pure <$> Gen.list (Range.linear 0 32) genItem

genInteger :: Gen Integer
genInteger = Gen.integral (Range.linear (-1024) 1024)

genListInteger :: Gen (ListT Identity Integer)
genListInteger = genList genInteger

double :: Integer -> Integer
double x = x + x

square :: Integer -> Integer
square x = x * x

showListT :: Show a => ListT Identity a -> String
showListT = show . toList . fmap show

toList :: ListT Identity a -> [a]
toList = Foldable.toList

onList :: ([a] -> [a] -> r) -> ListT Identity a -> ListT Identity a -> r
onList f = Function.on f toList

hprop_Functor_Identity :: Property
hprop_Functor_Identity = property $ do
    xs <- forAllWith showListT genListInteger
    onList (===) (id xs) (fmap id xs)

hprop_Functor_Composition :: Property
hprop_Functor_Composition = property $ do
    xs <- forAllWith showListT genListInteger
    onList (===)
        (fmap (double . square)      xs)
        ((fmap double . fmap square) xs)

hprop_Applicative_Identity :: Property
hprop_Applicative_Identity = property $ do
    v <- forAllWith showListT genListInteger
    onList (===) v (pure id <*> v)

hprop_Applicative_Composition :: Property
hprop_Applicative_Composition = property $ do
    u <- fmap (+) <$> forAllWith showListT genListInteger
    v <- fmap (*) <$> forAllWith showListT genListInteger
    w <- forAllWith showListT genListInteger
    onList (===)
        (pure (.) <*> u <*> v <*> w)
        (u <*> (v <*> w))

hprop_Applicative_Homomorphism :: Property
hprop_Applicative_Homomorphism = property $ do
    x <- forAll genInteger
    onList (===)
        (pure double <*> pure x)
        (pure (double x))
    onList (===)
        (pure square <*> pure x)
        (pure (square x))

hprop_Applicative_Interchange :: Property
hprop_Applicative_Interchange = property $ do
    u <- fmap (+) <$> forAllWith showListT genListInteger
    y <- forAll genInteger
    onList (===)
        (u <*> pure y)
        (pure ($ y) <*> u)

hprop_Alternative_Identity :: Property
hprop_Alternative_Identity = property $ do
    u <- forAllWith showListT genListInteger
    onList (===) u (empty <|> u)
    onList (===) u (u <|> empty)

hprop_Alternative_Annihilator :: Property
hprop_Alternative_Annihilator = property $ do
    u <- fmap (+) <$> forAllWith showListT genListInteger
    onList (===) empty (u <*> empty)

hprop_Alternative_Associative :: Property
hprop_Alternative_Associative = property $ do
    xs <- forAllWith showListT genListInteger
    ys <- forAllWith showListT genListInteger
    zs <- forAllWith showListT genListInteger
    onList (===) ((xs <|> ys) <|> zs) (xs <|> (ys <|> zs))

hprop_Monad_LeftUnit :: Property
hprop_Monad_LeftUnit = property $ do
    k <- (\xs y -> fmap (+ y) xs) <$> forAllWith showListT genListInteger
    a <- forAll genInteger
    onList (===) (k a) (return a >>= k)

hprop_Monad_RightUnit :: Property
hprop_Monad_RightUnit = property $ do
    m <- forAllWith showListT genListInteger
    onList (===) m (m >>= return)

hprop_Monad_Associative :: Property
hprop_Monad_Associative = property $ do
    k <- (\xs y -> fmap (+ y) xs) <$> forAllWith showListT genListInteger
    h <- (\xs y -> fmap (+ y) xs) <$> forAllWith showListT genListInteger
    m <- forAllWith showListT genListInteger
    onList (===) (m >>= (\x -> k x >>= h)) ((m >>= k) >>= h)

test_ListT_Reader :: [TestTree]
test_ListT_Reader =
    [ test' "local ask" [1] (local ask)
    , test' "local ask >> ask" [0] (local ask >> ask)
    , test' "ask <|> local ask" [0, 1] (ask <|> local ask)
    ]
  where
    local = Reader.local (const 1)
    ask = Reader.ask
    test' :: String -> [Integer] -> ListT (Reader Integer) Integer -> TestTree
    test' name expect run =
        let actual = Reader.runReader (ListT.gather run) 0
        in testCase name (assertEqual "" expect actual)
