module Test.Kore.Variables.Fresh (test_refreshVariable) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Set as Set
import           Data.Sup

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.Sort
import Kore.Variables.Fresh

import Test.Kore

metaVariable :: Variable Meta
metaVariable = Variable
    { variableName = testId "#v"
    , variableCounter = mempty
    , variableSort = SortVariableSort (SortVariable (testId "#s"))
    }

metaFreshVariableDifferentSort :: Variable Meta
metaFreshVariableDifferentSort = Variable
    { variableName = testId "#v"
    , variableCounter = Just (Element 100)
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

    , testCase "refreshVariable - keep same sort" $
        assertBool "Expected a fresh variable with the same sort"
            (variableSort fresh2 == variableSort original)
    ]
  where
    original = metaVariable
    avoid0 = Set.singleton original
    Just fresh0 = refreshVariable avoid0 original
    avoid1 = Set.insert fresh0 avoid0
    Just fresh1 = refreshVariable avoid1 original
    avoid2 = Set.insert metaFreshVariableDifferentSort avoid1
    Just fresh2 = refreshVariable avoid2 original
