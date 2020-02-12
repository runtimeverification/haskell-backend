module Test.Kore.Variables.Target
    ( test_Eq
    , test_Ord
    , test_Hashable
    ) where

import Prelude.Kore

import Hedgehog
import Test.Tasty
import Test.Tasty.Hedgehog

import Data.Hashable
    ( hash
    )

import Kore.Internal.Variable
import Kore.Sort
import Kore.Variables.Target

import Test.Kore
    ( elementVariableGen
    , standaloneGen
    , testId
    )

test_Eq :: [TestTree]
test_Eq =
    [ testProperty "(==) ignores constructor" $ Hedgehog.property $ do
        x <- forAll genElementVariable
        mkElementTarget x === mkElementNonTarget x
    ]

test_Ord :: [TestTree]
test_Ord =
    [ testProperty "(compare) ignores constructor" $ Hedgehog.property $ do
        x <- forAll genElementVariable
        y <- forAll genElementVariable
        compare x y === compare (mkElementTarget    x) (mkElementTarget    y)
        compare x y === compare (mkElementTarget    x) (mkElementNonTarget y)
        compare x y === compare (mkElementNonTarget x) (mkElementNonTarget y)
        compare x y === compare (mkElementNonTarget x) (mkElementTarget    y)
    ]

test_Hashable :: [TestTree]
test_Hashable =
    [ testProperty "(hash) ignores constructor" $ Hedgehog.property $ do
        x <- forAll genElementVariable
        hash (mkElementTarget x) === hash (mkElementNonTarget x)
    ]

aSort :: Sort
aSort =
    SortActualSort SortActual
        { sortActualName  = testId "A"
        , sortActualSorts = []
        }

genElementVariable :: Gen (ElementVariable Variable)
genElementVariable = standaloneGen $ elementVariableGen aSort
