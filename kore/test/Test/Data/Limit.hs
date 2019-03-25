module Test.Data.Limit
    ( prop_append
    , prop_dominate
    , prop_homomorphism
    , prop_identity
    ) where

import Test.Tasty.QuickCheck

import Data.Limit

limit :: Integer -> Limit Integer
limit = Limit

prop_dominate :: Integer -> Property
prop_dominate a =
    (.&&.)
    (compare (limit a) Unlimited === LT)
    (compare Unlimited (limit a) === GT)

prop_homomorphism :: Integer -> Integer -> Property
prop_homomorphism a b =
    compare (limit a) (limit b) === compare a b

prop_append :: Integer -> Integer -> Property
prop_append (limit -> a) (limit -> b) = a <> b === min a b

prop_identity :: Integer -> Property
prop_identity (limit -> a) =
    (.&&.)
    (mappend mempty a === a)
    (mappend a mempty === a)
