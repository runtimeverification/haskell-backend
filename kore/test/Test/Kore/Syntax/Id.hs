module Test.Kore.Syntax.Id
    ( test_Id
    ) where

import Test.Tasty

import Data.Function
import Data.Hashable

import Kore.Syntax.Id

import Test.Kore
    ( testId
    )
import Test.Terse

test_Id :: [TestTree]
test_Id =
    [ equals (testId "x") (noLocationId "x") "Eq"
    , on equals hash (testId "x") (noLocationId "x") "Hashable"
    ]
