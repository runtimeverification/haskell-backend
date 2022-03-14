module Test.Kore.Variables.Target (
    test_Eq,
    test_Ord,
    test_Hashable,
    test_FreshPartialOrd,
    test_FreshName,
) where

import Control.Monad qualified as Monad
import Data.Set qualified as Set
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Kore.Internal.Variable
import Kore.Sort
import Kore.Variables.Target
import Pair
import Prelude.Kore
import Test.Kore (
    elementVariableGen,
    standaloneGen,
    testId,
 )
import Test.Kore.Variables.Fresh
import Test.Tasty
import Test.Tasty.Hedgehog

test_Eq :: [TestTree]
test_Eq =
    [ testPropertyNamed "(==) ignores constructor" "" $
        Hedgehog.property $ do
            x <- forAll genElementVariable
            mkElementTarget x === mkElementNonTarget x
    ]

test_Ord :: [TestTree]
test_Ord =
    [ testPropertyNamed "(compare) ignores constructor" "" $
        Hedgehog.property $ do
            x <- forAll genElementVariable
            y <- forAll genElementVariable
            compare x y === compare (mkElementTarget x) (mkElementTarget y)
            compare x y === compare (mkElementTarget x) (mkElementNonTarget y)
            compare x y === compare (mkElementNonTarget x) (mkElementNonTarget y)
            compare x y === compare (mkElementNonTarget x) (mkElementTarget y)
    ]

test_Hashable :: [TestTree]
test_Hashable =
    [ testPropertyNamed "(hash) ignores constructor" "" $
        Hedgehog.property $ do
            x <- forAll genElementVariable
            hash (mkElementTarget x) === hash (mkElementNonTarget x)
    ]

test_FreshPartialOrd :: TestTree
test_FreshPartialOrd =
    testGroup "instance FreshPartialOrd (Target VariableName)" $
        testFreshPartialOrd $
            targetVariableNameGen relatedVariableNameGen

test_FreshName :: [TestTree]
test_FreshName =
    [ testGroup
        "instance FreshName (Target VariableName)"
        [ testPropertyNamed
            "Target avoids Target"
            ""
            (prop genTargetTarget isTarget)
        , testPropertyNamed
            "Target avoids NonTarget"
            ""
            (prop genTargetNonTarget isTarget)
        , testPropertyNamed
            "NonTarget avoids Target"
            ""
            (prop genNonTargetTarget isNonTarget)
        , testPropertyNamed
            "NonTarget avoids NonTarget"
            ""
            (prop genNonTargetNonTarget isNonTarget)
        ]
    , testGroup
        "instance FreshName (SomeVariableName (Target VariableName))"
        [ testPropertyNamed
            "Target avoids Target"
            ""
            (prop (genSomeElement genTargetTarget) isSomeTargetName)
        , testPropertyNamed
            "Target avoids NonTarget"
            ""
            (prop (genSomeElement genTargetNonTarget) isSomeTargetName)
        , testPropertyNamed
            "NonTarget avoids Target"
            ""
            (prop (genSomeElement genNonTargetTarget) isSomeNonTargetName)
        , testPropertyNamed
            "NonTarget avoids NonTarget"
            ""
            (prop (genSomeElement genNonTargetNonTarget) isSomeNonTargetName)
        ]
    ]
  where
    genTargetTarget = fmap Target <$> variableNameGen

    genNonTargetNonTarget = fmap NonTarget <$> variableNameGen

    genTargetNonTarget = do
        Pair x y <- variableNameGen
        pure (Pair (Target x) (NonTarget y))

    genNonTargetTarget = do
        Pair x y <- variableNameGen
        pure (Pair (NonTarget x) (Target y))

    genSomeElement :: Gen (Pair name) -> Gen (Pair (SomeVariableName name))
    genSomeElement gen = fmap (inject . ElementVariableName) <$> gen

    prop ::
        (FreshName x, Show x) =>
        Gen (Pair x) ->
        (x -> Bool) ->
        Property
    prop gen assertion = Hedgehog.property $ do
        Pair x y <- forAll gen
        let actual = refreshName (Set.singleton y) x
        case actual of
            Nothing -> x /== y
            Just x' -> do
                Hedgehog.annotateShow x'
                x === y
                Hedgehog.assert (assertion x')

targetVariableNameGen ::
    Gen (Pair variable) ->
    Gen (Pair (Target variable))
targetVariableNameGen gen = do
    Pair x y <- gen
    Gen.element
        [ Pair (Target x) (Target y)
        , Pair (Target x) (NonTarget y)
        , Pair (NonTarget x) (Target y)
        , Pair (NonTarget x) (NonTarget y)
        ]

variableNameGen :: Gen (Pair VariableName)
variableNameGen = do
    xy@(Pair x y) <- relatedVariableNameGen
    Monad.guard (x < maxBoundName x)
    Monad.guard (y < maxBoundName y)
    pure xy

aSort :: Sort
aSort =
    SortActualSort
        SortActual
            { sortActualName = testId "A"
            , sortActualSorts = []
            }

genElementVariable :: Gen (ElementVariable VariableName)
genElementVariable = standaloneGen $ elementVariableGen aSort
