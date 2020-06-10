module Test.Kore.Variables.Target
    ( test_Eq
    , test_Ord
    , test_Hashable
    , test_FreshPartialOrd
    , test_FreshName
    ) where

import Prelude.Kore

import Hedgehog
import qualified Hedgehog.Gen as Gen
import Test.Tasty
import Test.Tasty.Hedgehog

import qualified Data.Set as Set

import Kore.Internal.Variable
import Kore.Sort
import Kore.Variables.Target
import Pair

import Test.Kore
    ( elementVariableGen
    , standaloneGen
    , testId
    )
import Test.Kore.Variables.Fresh

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

test_FreshPartialOrd :: TestTree
test_FreshPartialOrd =
    testGroup "instance FreshPartialOrd (Target VariableName)"
    $ testFreshPartialOrd
    $ targetVariableNameGen relatedVariableNameGen

test_FreshName :: TestTree
test_FreshName =
    testGroup "instance FreshName (Target VariableName)"
    [ testProperty "Target avoids Target" $ Hedgehog.property $ do
        Pair x y <- forAll relatedVariableNameGen
        let actual = refreshName (Set.singleton (Target y)) (Target x)
        case actual of
            Nothing -> x /== y
            Just x' -> do
                Hedgehog.annotateShow x'
                x === y
                Hedgehog.assert (isTarget x')
    , testProperty "Target avoids NonTarget" $ Hedgehog.property $ do
        Pair x y <- forAll relatedVariableNameGen
        let actual = refreshName (Set.singleton (NonTarget y)) (Target x)
        case actual of
            Nothing -> x /== y
            Just x' -> do
                Hedgehog.annotateShow x'
                x === y
                Hedgehog.assert (isTarget x')
    , testProperty "NonTarget avoids Target" $ Hedgehog.property $ do
        Pair x y <- forAll relatedVariableNameGen
        let actual = refreshName (Set.singleton (Target y)) (NonTarget x)
        case actual of
            Nothing -> x /== y
            Just x' -> do
                Hedgehog.annotateShow x'
                x === y
                Hedgehog.assert (isNonTarget x')
    , testProperty "NonTarget avoids NonTarget" $ Hedgehog.property $ do
        Pair x y <- forAll relatedVariableNameGen
        let actual = refreshName (Set.singleton (NonTarget y)) (NonTarget x)
        case actual of
            Nothing -> x /== y
            Just x' -> do
                Hedgehog.annotateShow x'
                x === y
                Hedgehog.assert (isNonTarget x')
    ]

targetVariableNameGen
    :: Gen (Pair variable)
    -> Gen (Pair (Target variable))
targetVariableNameGen gen = do
    Pair x y <- gen
    Gen.element
        [ Pair (Target x) (Target y)
        , Pair (Target x) (NonTarget y)
        , Pair (NonTarget x) (Target y)
        , Pair (NonTarget x) (NonTarget y)
        ]

aSort :: Sort
aSort =
    SortActualSort SortActual
        { sortActualName  = testId "A"
        , sortActualSorts = []
        }

genElementVariable :: Gen (ElementVariable VariableName)
genElementVariable = standaloneGen $ elementVariableGen aSort
