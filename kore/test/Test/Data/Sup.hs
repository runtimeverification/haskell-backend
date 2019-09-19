module Test.Data.Sup where

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Control.Monad

import Data.Sup

genSup :: Gen a -> Gen (Sup a)
genSup genA = Gen.choice [ pure Sup, Element <$> genA ]

genSmallInteger :: Gen Integer
genSmallInteger = Gen.integral (Range.linear (-3) 3)

genSupInteger :: Gen (Sup Integer)
genSupInteger = genSup genSmallInteger

sups :: [Sup Integer]
sups = Sup : map Element [(-3)..3]

implies :: Monad m => Bool -> Bool -> PropertyT m ()
implies lhs rhs = when lhs (Hedgehog.assert rhs)

hprop_transitiveOrd :: Property
hprop_transitiveOrd =
    (property . sequence_)
        (transitive <$> sups <*> sups <*> sups)
  where
    transitive x y z = do
        annotateShow (x, y, z)
        implies ((x <= y) && (y <= z)) (x <= z)

hprop_reflexiveOrd :: Property
hprop_reflexiveOrd =
    (property . sequence_)
        (reflexive <$> sups)
  where
    reflexive x = do
        annotateShow x
        Hedgehog.assert (x <= x)

hprop_antisymmetricOrd :: Property
hprop_antisymmetricOrd =
    (property . sequence_)
        (antisymmetric <$> sups <*> sups)
  where
    antisymmetric x y = do
        annotateShow (x, y)
        implies ((x <= y) && (y <= x)) (x == y)

hprop_reflexiveEq :: Property
hprop_reflexiveEq =
    (property . sequence_)
        (reflexive <$> sups)
  where
    reflexive x = do
        annotateShow x
        Hedgehog.assert (x == x)

hprop_symmetricEq :: Property
hprop_symmetricEq =
    (property . sequence_)
        (symmetric <$> sups <*> sups)
  where
    symmetric x y = do
        annotateShow (x, y)
        (x == y) === (y == x)

hprop_transitiveEq :: Property
hprop_transitiveEq =
    (property . sequence_)
        (transitive <$> sups <*> sups <*> sups)
  where
    transitive x y z = do
        annotateShow (x, y, z)
        implies ((x == y) && (y == z)) (x == z)

hprop_negativeEq :: Property
hprop_negativeEq =
    (property . sequence_)
        (negative <$> sups <*> sups)
  where
    negative x y = do
        annotateShow (x, y)
        (x /= y) === not (x == y)

hprop_associativeSemigroup :: Property
hprop_associativeSemigroup = property $ do
    x <- forAll genSupInteger
    y <- forAll genSupInteger
    z <- forAll genSupInteger
    (x <> (y <> z)) === (x <> y) <> z

hprop_commutativeSemigroup :: Property
hprop_commutativeSemigroup = property $ do
    x <- forAll genSupInteger
    y <- forAll genSupInteger
    (x <> y) === (y <> x)

hprop_idempotentSemigroup :: Property
hprop_idempotentSemigroup = property $ do
    x <- forAll genSupInteger
    (x <> x) === x

hprop_identityFunctor :: Property
hprop_identityFunctor = property $ do
    x <- forAll genSupInteger
    fmap id x === x

hprop_compositionFunctor :: Property
hprop_compositionFunctor = property $ do
    x <- forAll genSupInteger
    f <- (+) <$> forAll genSmallInteger
    g <- (*) <$> forAll genSmallInteger
    fmap (f . g) x === (fmap f . fmap g) x

hprop_identityApplicative :: Property
hprop_identityApplicative = property $ do
    x <- forAll genSupInteger
    (pure id <*> x) === x

hprop_compositionApplicative :: Property
hprop_compositionApplicative = property $ do
    u <- fmap (+) <$> forAll genSupInteger
    v <- fmap (*) <$> forAll genSupInteger
    w <- forAll genSupInteger
    (pure (.) <*> u <*> v <*> w) === (u <*> (v <*> w))

hprop_homomorphismApplicative :: Property
hprop_homomorphismApplicative = property $ do
    x <- forAll genSmallInteger
    f <- (+) <$> forAll genSmallInteger
    (pure f <*> pure x :: Sup Integer) === pure (f x)

hprop_interchangeApplicative :: Property
hprop_interchangeApplicative = property $ do
    u <- fmap (+) <$> forAll genSupInteger
    y <- forAll genSmallInteger
    (u <*> pure y) === (pure ($ y) <*> u)
