module Test.Kore.Variables.Fresh (test_refreshVariable) where

import Test.Tasty
import Test.Tasty.HUnit

import Data.Maybe
    ( isJust
    )
import qualified Data.Set as Set

import Kore.Sort
import Kore.Variables.Fresh

import Test.Kore

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
