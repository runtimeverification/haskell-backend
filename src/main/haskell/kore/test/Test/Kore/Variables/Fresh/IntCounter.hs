module Test.Kore.Variables.Fresh.IntCounter (test_intCounter) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, assertFailure, testCase )

import Control.Exception
       ( ErrorCall (ErrorCall), catch, evaluate )
import Control.Monad.State
       ( modify )

import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.Variables.Fresh.Class
import Kore.Variables.Fresh.IntCounter

import Test.Kore

objectVariable :: Variable Object
objectVariable = Variable
    { variableName = testId "v"
    , variableSort = SortVariableSort (SortVariable (testId "s"))
    }

metaVariable :: Variable Meta
metaVariable = Variable
    { variableName = testId "#v"
    , variableSort = SortVariableSort (SortVariable (testId "#s"))
    }

test_intCounter :: [TestTree]
test_intCounter =
    [ testCase "Testing freshVariable Object 2"
        (assertEqual ""
            (objectVariable { variableName = testId "var_2" }, 3)
            (runIntCounter (freshVariable objectVariable) 2)
        )
    , testCase "Testing freshVariable Meta 2"
        (assertEqual ""
            (metaVariable { variableName = testId "#var_2" }, 3)
            (runIntCounter (freshVariable metaVariable) 2)
        )
    , testCase "Testing freshVariable Functor Meta 1"
        (assertEqual ""
            (( metaVariable { variableName = testId "#var_1" }
              , metaVariable { variableName = testId "#var_2" }), 3)
            (runIntCounter
                ((,)
                    <$> freshVariable metaVariable
                    <*> freshVariable metaVariable
                ) 1)
          )
    , testCase "Testing freshUnifiedVariable Meta 2"
        (assertEqual ""
            (metaVariable { variableName = testId "#var_2" }, 3)
            (runIntCounter
                (freshVariable metaVariable) 2)
        )
    , testCase "Testing failing freshVariableSuchThat Meta 1"
        ((evaluate (runIntCounter
                (freshVariableSuchThat
                    metaVariable
                    (== metaVariable)
                ) 2) >> assertFailure "This evaluation should fail")
            `catch` \ (ErrorCall s) ->
                    assertEqual ""
                        "Cannot generate variable satisfying predicate"
                        s
        )
    , testCase "Testing freshVariableSuchThat Meta 1"
        (assertEqual ""
            (metaVariable { variableName = testId "#var_2" }, 3)
            (runIntCounter
                (freshVariableSuchThat
                    metaVariable
                    (const True)
                ) 2)
        )
    , testCase "Testing succesful findState"
        (assertEqual ""
            (Just 1, 7)
            (runIntCounter
                (findState (>0)
                    [action (-1), action 0, action 1, action (-2), action 1]
                )
                6
            )
        )
    , testCase "Testing unsuccesful findState"
        (assertEqual ""
            (Nothing, 6)
            (runIntCounter
                (findState (>1)
                    [action (-1), action 0, action 1, action (-2), action 1]
                )
                6
            )
        )
    ]
  where
    action :: Int -> IntCounter Int
    action n = do
        modify (+1)
        return n


