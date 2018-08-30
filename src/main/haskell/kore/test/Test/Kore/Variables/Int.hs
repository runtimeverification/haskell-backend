module Test.Kore.Variables.Int (test_int) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.Variables.Int

import Test.Kore

test_int :: [TestTree]
test_int =
    [ testCase "Testing intVariable Object 1"
        (assertEqual ""
            (Variable
                { variableName = testId "var_1"
                , variableSort =
                    SortVariableSort (SortVariable (testId "s"))
                }::Variable Object)
            (intVariable Variable
                { variableName = testId "v"
                , variableSort =
                    SortVariableSort (SortVariable (testId "s"))
                }
                1)
        )
    , testCase "Testing intVariable Meta 1"
        (assertEqual ""
            (Variable
                { variableName = testId "#var_1"
                , variableSort =
                    SortVariableSort (SortVariable (testId "#s"))
                }:: Variable Meta)
            (intVariable Variable
                  { variableName = testId "#v"
                  , variableSort =
                    SortVariableSort (SortVariable (testId "#s"))
                  }
            1)
        )
    ]
