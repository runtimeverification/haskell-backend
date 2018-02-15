module Data.Kore.FreshVariables.IntTest where

import           Test.Tasty                   (TestTree, testGroup)
import           Test.Tasty.HUnit             (Assertion, assertBool,
                                               assertEqual, assertFailure,
                                               testCase)

import           Control.Exception            (ErrorCall (ErrorCall), catch,
                                               evaluate)

import           Data.Kore.AST
import           Data.Kore.FreshVariables.Int


testLift :: FreshVariablesT IO ()
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

freshVariablesIntTests :: TestTree
freshVariablesIntTests =
    testGroup
        "FreshVariables.Int Tests"
        [ testCase "Testing intVariable Object 1."
            (assertEqual ""
                objectVariable { variableName = Id "var1" }
                (intVariable objectVariable 1)
            )
        , testCase "Testing freshVariable Object 2."
            (assertEqual ""
                (objectVariable { variableName = Id "var2" }, 3)
                (runFreshVariables (freshVariable objectVariable) 2)
            )
        , testCase "Testing intVariable Meta 1."
            (assertEqual ""
                metaVariable { variableName = Id "#var1" }
                (intVariable metaVariable 1)
            )
        , testCase "Testing freshVariable Meta 2."
            (assertEqual ""
                (metaVariable { variableName = Id "#var2" }, 3)
                (runFreshVariables (freshVariable metaVariable) 2)
            )
        , testCase "Testing freshVariable Functor Meta 1."
            (assertEqual ""
                (( metaVariable { variableName = Id "#var1" }
                 , metaVariable { variableName = Id "#var2" }), 3)
                (runFreshVariables
                    ((,)
                        <$> freshVariable metaVariable
                        <*> freshVariable metaVariable
                    ) 1)
             )
        , testCase "Testing freshUnifiedVariable Meta 2."
            (assertEqual ""
                (MetaVariable $ metaVariable { variableName = Id "#var2" }, 3)
                (runFreshVariables
                    (freshUnifiedVariable unifiedMetaVariable) 2)
            )
        , testCase "Testing failing freshVariableSuchThat Meta 1."
            ((evaluate (runFreshVariables
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
                (runFreshVariables
                    (freshVariableSuchThat
                        unifiedMetaVariable
                        (const True)
                    ) 2)
            )
        , testCase "Testing lift" (fst <$> (runFreshVariablesT testLift 17))
           ]
