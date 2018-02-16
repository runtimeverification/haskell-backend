module Data.Kore.Variables.Fresh.IntCounterTest where

import           Test.Tasty                           (TestTree, testGroup)
import           Test.Tasty.HUnit                     (assertBool, assertEqual,
                                                       assertFailure, testCase)

import           Control.Exception                    (ErrorCall (ErrorCall),
                                                       catch, evaluate)
import           Control.Monad.Trans                  (lift)

import           Data.Kore.AST
import           Data.Kore.Variables.Fresh.Class
import           Data.Kore.Variables.Fresh.IntCounter

testLift :: IntCounterT IO ()
testLift = lift (assertBool "" True)

objectVariable :: Variable Object
objectVariable = Variable
    { variableName = Id "v"
    , variableSort = SortVariableSort (SortVariable (Id "s"))
    }

metaVariable :: Variable Meta
metaVariable = Variable
    { variableName = Id "#v"
    , variableSort = SortVariableSort (SortVariable (Id "#s"))
    }

unifiedMetaVariable :: UnifiedVariable Variable
unifiedMetaVariable = MetaVariable metaVariable

variablesFreshIntCounterTests :: TestTree
variablesFreshIntCounterTests =
    testGroup
        "Variables.Fresh.IntCounter Tests"
        [ testCase "Testing freshVariable Object 2."
            (assertEqual ""
                (objectVariable { variableName = Id "var2" }, 3)
                (runIntCounter (freshVariable objectVariable) 2)
            )
        , testCase "Testing freshVariable Meta 2."
            (assertEqual ""
                (metaVariable { variableName = Id "#var2" }, 3)
                (runIntCounter (freshVariable metaVariable) 2)
            )
        , testCase "Testing freshVariable Functor Meta 1."
            (assertEqual ""
                (( metaVariable { variableName = Id "#var1" }
                 , metaVariable { variableName = Id "#var2" }), 3)
                (runIntCounter
                    ((,)
                        <$> freshVariable metaVariable
                        <*> freshVariable metaVariable
                    ) 1)
             )
        , testCase "Testing freshUnifiedVariable Meta 2."
            (assertEqual ""
                (MetaVariable $ metaVariable { variableName = Id "#var2" }, 3)
                (runIntCounter
                    (freshUnifiedVariable unifiedMetaVariable) 2)
            )
        , testCase "Testing failing freshVariableSuchThat Meta 1."
            ((evaluate (runIntCounter
                    (freshVariableSuchThat
                        unifiedMetaVariable
                        (== unifiedMetaVariable)
                    ) 2) >> assertFailure "This evaluation should fail")
                `catch` \ (ErrorCall s) ->
                        assertEqual ""
                            "Cannot generate variable satisfying predicate"
                            s
            )
        , testCase "Testing failing freshVariableSuchThat Meta 1."
            (assertEqual ""
                (MetaVariable $ metaVariable { variableName = Id "#var2" }, 3)
                (runIntCounter
                    (freshVariableSuchThat
                        unifiedMetaVariable
                        (const True)
                    ) 2)
            )
        , testCase "Testing lift" (fst <$> runIntCounterT testLift 17)
           ]
