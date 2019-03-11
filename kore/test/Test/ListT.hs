module Test.ListT where

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import qualified Data.Foldable as Foldable
import qualified Data.Function as Function
import           Data.Functor.Identity

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

hprop_FunctorIdentity :: Property
hprop_FunctorIdentity = property $ do
    xs <- forAllWith showListT genListInteger
    onList (===) (id xs) (fmap id xs)

hprop_FunctorComposition :: Property
hprop_FunctorComposition = property $ do
    xs <- forAllWith showListT genListInteger
    onList (===)
        (fmap (double . square)      xs)
        ((fmap double . fmap square) xs)

hprop_ApplicativeIdentity :: Property
hprop_ApplicativeIdentity = property $ do
    v <- forAllWith showListT genListInteger
    onList (===) v (pure id <*> v)

hprop_ApplicativeComposition :: Property
hprop_ApplicativeComposition = property $ do
    u <- fmap (+) <$> forAllWith showListT genListInteger
    v <- fmap (*) <$> forAllWith showListT genListInteger
    w <- forAllWith showListT genListInteger
    onList (===)
        (pure (.) <*> u <*> v <*> w)
        (u <*> (v <*> w))

hprop_ApplicativeHomomorphism :: Property
hprop_ApplicativeHomomorphism = property $ do
    x <- forAll genInteger
    onList (===)
        (pure double <*> pure x)
        (pure (double x))
    onList (===)
        (pure square <*> pure x)
        (pure (square x))

hprop_ApplicativeInterchange :: Property
hprop_ApplicativeInterchange = property $ do
    u <- fmap (+) <$> forAllWith showListT genListInteger
    y <- forAll genInteger
    onList (===)
        (u <*> pure y)
        (pure ($ y) <*> u)

hprop_AlternativeIdentity :: Property
hprop_AlternativeIdentity = property $ do
    u <- forAllWith showListT genListInteger
    onList (===) u (empty <|> u)
    onList (===) u (u <|> empty)

hprop_AlternativeAnnihilator :: Property
hprop_AlternativeAnnihilator = property $ do
    u <- fmap (+) <$> forAllWith showListT genListInteger
    onList (===) empty (u <*> empty)

hprop_AlternativeAssociative :: Property
hprop_AlternativeAssociative = property $ do
    xs <- forAllWith showListT genListInteger
    ys <- forAllWith showListT genListInteger
    zs <- forAllWith showListT genListInteger
    onList (===) ((xs <|> ys) <|> zs) (xs <|> (ys <|> zs))

hprop_MonadLeftUnit :: Property
hprop_MonadLeftUnit = property $ do
    k <- (\xs y -> fmap (+ y) xs) <$> forAllWith showListT genListInteger
    a <- forAll genInteger
    onList (===) (k a) (return a >>= k)

hprop_MonadRightUnit :: Property
hprop_MonadRightUnit = property $ do
    m <- forAllWith showListT genListInteger
    onList (===) m (m >>= return)

hprop_MonadAssociative :: Property
hprop_MonadAssociative = property $ do
    k <- (\xs y -> fmap (+ y) xs) <$> forAllWith showListT genListInteger
    h <- (\xs y -> fmap (+ y) xs) <$> forAllWith showListT genListInteger
    m <- forAllWith showListT genListInteger
    onList (===) (m >>= (\x -> k x >>= h)) ((m >>= k) >>= h)
