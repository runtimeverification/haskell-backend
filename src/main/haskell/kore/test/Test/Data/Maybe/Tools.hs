module Test.Data.Maybe.Tools
    ( test_maybeTools
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import Data.Maybe.Tools
       ( firstMaybe )

test_maybeTools :: [TestTree]
test_maybeTools =
    [ testCase "firstMaybe" $ do
        assertEqual "empty list"
            (Nothing :: Maybe Integer)
            (firstMaybe [])
        assertEqual "many Nothings"
            (Nothing :: Maybe Integer)
            (firstMaybe [Nothing, Nothing, Nothing])
        assertEqual "existing value"
            (Just 3 :: Maybe Integer)
            (firstMaybe [Nothing, Nothing, Just 3, Nothing])
        assertEqual "multiple existing values"
            (Just 3 :: Maybe Integer)
            (firstMaybe [Nothing, Nothing, Just 3, Nothing, Just 4])
    ]
