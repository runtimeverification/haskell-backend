{-# OPTIONS_GHC -fno-warn-orphans #-}

module Test.Data.Result where

import Test.QuickCheck.Function
import Test.Tasty.QuickCheck hiding
       ( Failure, Success )

import Control.Applicative
       ( Alternative (..) )

import Data.Result

instance Arbitrary a => Arbitrary (Result a) where
    arbitrary = do
        n <- elements [0, 1, 2]
        case n :: Integer of
            0 -> Success <$> arbitrary
            1 -> return Failure
            _ -> return Unknown

    shrink (Success a) = Success <$> shrink a
    shrink _ = []

instance CoArbitrary a => CoArbitrary (Result a) where
    coarbitrary =
        \case
            Success a -> variant (0 :: Int) . coarbitrary a
            Failure -> variant (1 :: Int)
            Unknown -> variant (2 :: Int)

prop_biasSuccess :: Integer -> Result Integer -> Property
prop_biasSuccess a m =
    let r = Success a in (r <|> m) === r

prop_biasFailure :: Result Integer -> Property
prop_biasFailure m =
    let r = Failure in (r <|> m) === r

prop_identityAlternative :: Result Integer -> Property
prop_identityAlternative m =
    let r = Unknown in (r <|> m) === m

prop_leftUnitMonad :: Integer -> Fun Integer (Result Integer) -> Property
prop_leftUnitMonad a (applyFun -> k) = (return a >>= k) === (k a)

prop_rightUnitMonad :: Result Integer -> Property
prop_rightUnitMonad m = (m >>= return) === m

prop_assocMonad
    :: Result Integer
    -> Fun Integer (Result Integer)
    -> Fun Integer (Result Integer)
    -> Property
prop_assocMonad m (applyFun -> k) (applyFun -> h) =
    (m >>= (\x -> k x >>= h)) === ((m >>= k) >>= h)

prop_identityApplicative :: Result Integer -> Property
prop_identityApplicative v = (pure id <*> v) === v

prop_compositionApplicative
    :: Result (Fun Integer Integer)
    -> Result (Fun Integer Integer)
    -> Result Integer
    -> Property
prop_compositionApplicative (fmap applyFun -> u) (fmap applyFun -> v) w =
    (pure (.) <*> u <*> v <*> w) === (u <*> (v <*> w))

prop_homomorphismApplicative
    :: Fun Integer Integer
    -> Integer
    -> Property
prop_homomorphismApplicative (applyFun -> f) x =
    (pure f <*> pure x :: Result Integer) === pure (f x)

prop_interchangeApplicative :: Result (Fun Integer Integer) -> Integer -> Property
prop_interchangeApplicative (fmap applyFun -> u) y =
    (u <*> pure y) === (pure ($ y) <*> u)
