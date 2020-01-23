{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}

module Test.Kore.Variables.Fresh
    ( test_refreshVariable
    , test_freshVariableProperties
    ) where

import Hedgehog
    ( forAll
    )
import qualified Hedgehog as Property
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.HUnit

import Data.Maybe
    ( isJust
    )
import qualified Data.Set as Set

import Kore.Sort
import Kore.Variables.Fresh

import Test.Kore
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.SMT

metaVariable :: Variable
metaVariable = Variable
    { variableName = testId "#v"
    , variableCounter = mempty
    , variableSort = SortVariableSort (SortVariable (testId "#s"))
    }

metaVariableDifferentSort :: Variable
metaVariableDifferentSort = Variable
    { variableName = testId "#v"
    , variableCounter = mempty
    , variableSort = SortVariableSort (SortVariable (testId "#s1"))
    }

test_refreshVariable :: [TestTree]
test_refreshVariable =
    [ testCase "refreshVariable - avoid empty set" $
        assertEqual "Expected no new variable"
            Nothing
            (refreshVariable Set.empty original)

    , testCase "refreshVariable - avoid original" $
        assertBool "Expected fresh variable" (original < fresh0)

    , testCase "refreshVariable - avoid fresh" $
        assertBool "Expected another fresh variable"     (fresh0   < fresh1)

    , testCase "refreshVariable - expecting the same sort" $
        assertBool "Expected fresh variable has same sort as original"
            (variableSort original == variableSort fresh2)

    , testCase "refreshVariable - sort order does not matter" $
        let assertRefreshes a b =
                assertBool "Expected fresh variable"
                    (isJust (refreshVariable (Set.singleton a) b))
        in do
            assertRefreshes original metaVariableDifferentSort
            assertRefreshes metaVariableDifferentSort original
    ]
  where
    original = metaVariable
    avoid0 = Set.singleton original
    Just fresh0 = refreshVariable avoid0 original
    avoid1 = Set.insert fresh0 avoid0
    Just fresh1 = refreshVariable avoid1 original
    avoid2 = Set.singleton metaVariableDifferentSort
    Just fresh2 = refreshVariable avoid2 original

test_freshVariableProperties :: [TestTree]
test_freshVariableProperties =
    [ freshVariablePropertyTests
        "FreshVariable ElementVariable"
        (elementVariableGen Mock.testSort)
    , freshVariablePropertyTests
        "FreshVariable SetVariable"
        (setVariableGen Mock.testSort)
    , freshVariablePropertyTests
        "FreshVariable UnifiedVariable"
        (unifiedVariableGen Mock.testSort)
    ]

freshVariablePropertyTests
    :: FreshVariable variable
    => Show variable
    => String
    -> Gen variable
    -> TestTree
freshVariablePropertyTests suiteName generator =
    testPropertyWithoutSolver suiteName $ do
        var <- forAll (standaloneGen generator)
        varSet <-
            forAll
            $ Gen.set (Range.linear 0 50)
            $ standaloneGen generator
        let inf = infVariable var
            sup = supVariable var
            nextVar = nextVariable var
            nextNextVar = nextVariable nextVar
            freshVar = refreshVariable varSet var
        Property.assert (inf <= var && var < sup)
        Property.assert (var < nextVar && nextVar < nextNextVar)
        Property.assert (keepsSameSort freshVar var)
        Property.assert (neverReturnsSameVar freshVar var)
        Property.assert (returnsNewVar freshVar var varSet)
  where
    keepsSameSort Nothing _ = True
    keepsSameSort (Just var') var =
        sortedVariableSort var' == sortedVariableSort var

    neverReturnsSameVar Nothing _ = True
    neverReturnsSameVar (Just var') var =
        var' /= var

    returnsNewVar freshVar var varSet =
        not (Set.member var varSet)
        || isJust freshVar
