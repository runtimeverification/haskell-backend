{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Test.Kore.Variables.Fresh (
    test_refreshVariable,
    test_FreshPartialOrd_VariableName,
    test_FreshPartialOrd_ElementVariableName,
    test_FreshPartialOrd_SetVariableName,
    test_FreshPartialOrd_SomeVariableName,
    --
    testFreshPartialOrd,
    relatedVariableNameGen,
    someVariableNameGen,

    -- * Re-exports
    module Kore.Variables.Fresh,
) where

import qualified Control.Lens as Lens
import Data.Generics.Product (
    field,
 )
import Data.Maybe (
    fromJust,
 )
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import Data.Sup
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Kore.Sort
import Kore.Variables.Fresh
import Numeric.Natural
import Pair
import Prelude.Kore
import Test.Kore (
    idGen,
    testId,
 )
import Test.Kore.Rewrite.MockSymbols (
    testSort0,
    testSort1,
 )
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog

type Variable' = Variable VariableName

metaVariable :: Variable'
metaVariable =
    Variable
        { variableName = VariableName{base = testId "#v", counter = mempty}
        , variableSort = SortVariableSort (SortVariable (testId "#s"))
        }

metaVariableDifferentSort :: Variable'
metaVariableDifferentSort =
    Variable
        { variableName = VariableName{base = testId "#v", counter = mempty}
        , variableSort = SortVariableSort (SortVariable (testId "#s1"))
        }

test_refreshVariable :: [TestTree]
test_refreshVariable =
    [ testCase "same name, different sort" $ do
        let variableName =
                VariableName{base = testId "x0", counter = mempty}
            x0 =
                Variable
                    { variableName
                    , variableSort = testSort0
                    }
            x1 = x0{variableSort = testSort1}
            x1' =
                Lens.set
                    (field @"variableName" . field @"counter")
                    (Just (Element 0))
                    x1
        let avoiding = Set.singleton variableName
        assertEqual
            "Expected fresh variable"
            (Just x1')
            (refreshVariable avoiding x1)
    , testCase "refreshVariable - avoid empty set" $
        assertEqual
            "Expected no new variable"
            Nothing
            (refreshVariable Set.empty original)
    , testCase "refreshVariable - avoid original" $
        assertBool "Expected fresh variable" (original < fresh0 original)
    , testCase "refreshVariable - avoid fresh" $
        assertBool
            "Expected another fresh variable"
            (fresh0 original < fresh1 original)
    , testCase "refreshVariable - expecting the same sort" $
        assertBool
            "Expected fresh variable has same sort as original"
            (variableSort original == variableSort fresh2)
    , testCase "refreshVariable - sort order does not matter" $ do
        let assertRefreshes (variableName -> a) b =
                assertBool
                    "Expected fresh variable"
                    (isJust (refreshVariable (Set.singleton a) b))
        assertRefreshes original metaVariableDifferentSort
        assertRefreshes metaVariableDifferentSort original
    ]
  where
    original = metaVariable
    avoid2 = Set.singleton (variableName metaVariableDifferentSort)
    Just fresh2 = refreshVariable avoid2 original

    avoid0 :: Variable variable -> Set variable
    avoid0 = Set.singleton . variableName

    avoid1 :: FreshName variable => Variable variable -> Set variable
    avoid1 variable =
        Set.insert (variableName $ fresh0 variable) (avoid0 variable)

    fresh0
        , fresh1 ::
            FreshName variable =>
            Variable variable ->
            Variable variable
    fresh0 var = fromJust $ refreshVariable (avoid0 var) var
    fresh1 var = fromJust $ refreshVariable (avoid1 var) var

{- | Property tests of a 'FreshPartialOrd' instance using the given generator.

The generator should produce a 'Pair' of related variables.
-}
testFreshPartialOrd ::
    (Show variable, FreshPartialOrd variable) =>
    Gen (Pair variable) ->
    [TestTree]
testFreshPartialOrd gen =
    [ testProperty "exclusive bounds" $
        property $ do
            xy <- forAll gen
            let Pair infX infY = minBoundName <$> xy
                Pair supX supY = maxBoundName <$> xy
            annotateShow infX
            annotateShow supX
            annotateShow infY
            annotateShow supY
            (infX == infY) === (supX == supY)
            infX /== supY
            infY /== supX
    , testProperty "lower and upper bound" $
        property $ do
            Pair x _ <- forAll gen
            let inf = minBoundName x
                sup = maxBoundName x
            annotateShow inf
            annotateShow sup
            Hedgehog.assert (inf <= x)
            Hedgehog.assert (x <= sup)
            Hedgehog.assert (inf < sup)
    , testProperty "idempotence" $
        property $ do
            Pair x _ <- forAll gen
            let inf1 = minBoundName x
                inf2 = minBoundName inf1
                sup1 = maxBoundName x
                sup2 = maxBoundName sup1
            inf1 === inf2
            sup1 === sup2
    , testProperty "nextName" $
        property $ do
            Pair x _ <- forAll gen
            let inf = minBoundName x
                sup = maxBoundName x
                ~next = nextName x x
            unless (x < sup) discard
            annotateShow inf
            annotateShow sup
            annotateShow next
            Hedgehog.assert (Just inf < next)
            Hedgehog.assert (Just x < next)
            Hedgehog.assert (next < Just sup)
    ]

counterGen :: MonadGen gen => gen (Maybe (Sup Natural))
counterGen =
    Gen.frequency
        [ (2, pure Nothing)
        , (4, Just . Element <$> Gen.integral (Range.linear 0 256))
        , (1, pure $ Just Sup)
        ]

test_FreshPartialOrd_VariableName :: TestTree
test_FreshPartialOrd_VariableName =
    testGroup "instance FreshPartialOrd VariableName" $
        testFreshPartialOrd relatedVariableNameGen

relatedVariableNameGen :: Gen (Pair VariableName)
relatedVariableNameGen = do
    Pair name1 name2 <-
        Gen.choice
            [ do name <- idGen; return (Pair name name)
            , Pair <$> idGen <*> idGen
            ]
    Pair counter1 counter2 <-
        Gen.choice
            [ do counter <- counterGen; return (Pair counter counter)
            , Pair <$> counterGen <*> counterGen
            ]
    let variable1 = VariableName name1 counter1
        variable2 = VariableName name2 counter2
    return (Pair variable1 variable2)

test_FreshPartialOrd_ElementVariableName :: TestTree
test_FreshPartialOrd_ElementVariableName =
    testGroup "instance FreshPartialOrd (ElementVariableName VariableName)" $
        testFreshPartialOrd $
            (fmap . fmap) ElementVariableName relatedVariableNameGen

test_FreshPartialOrd_SetVariableName :: TestTree
test_FreshPartialOrd_SetVariableName =
    testGroup "instance FreshPartialOrd (SetVariableName VariableName)" $
        testFreshPartialOrd $
            (fmap . fmap) SetVariableName relatedVariableNameGen

test_FreshPartialOrd_SomeVariableName :: TestTree
test_FreshPartialOrd_SomeVariableName =
    testGroup "instance FreshPartialOrd (SomeVariableName VariableName)" $
        testFreshPartialOrd $
            someVariableNameGen relatedVariableNameGen

someVariableNameGen ::
    Gen (Pair variable) ->
    Gen (Pair (SomeVariableName variable))
someVariableNameGen gen =
    Gen.choice
        [ (fmap . fmap) (inject . ElementVariableName) gen
        , (fmap . fmap) (inject . SetVariableName) gen
        ]
