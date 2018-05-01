module Data.Kore.Variables.IntTest where

import           Test.Tasty                 (TestTree, testGroup)
import           Test.Tasty.HUnit           (assertEqual, testCase)

import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.Variables.Int

variablesIntTests :: TestTree
variablesIntTests =
    testGroup
        "FreshVariables.Int Tests"
        [ testCase "Testing intVariable Object 1."
            (assertEqual ""
                (Variable
                    { variableName = Id "var_1"
                    , variableSort = SortVariableSort (SortVariable (Id "s"))
                    }::Variable Object)
                (intVariable Variable
                    { variableName = Id "v"
                    , variableSort = SortVariableSort (SortVariable (Id "s"))
                    }
                    1)
            )
        , testCase "Testing intVariable Meta 1."
            (assertEqual ""
                (Variable
                    { variableName = Id "#var_1"
                    , variableSort = SortVariableSort (SortVariable (Id "#s"))
                    }:: Variable Meta)
                (intVariable Variable
                     { variableName = Id "#v"
                     , variableSort = SortVariableSort (SortVariable (Id "#s"))
                     }
                1)
            )
       ]
