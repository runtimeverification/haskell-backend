module Data.Kore.FreshVariables.IntTest where

import           Test.Tasty                   (TestTree, testGroup)
import           Test.Tasty.HUnit             (assertEqual, assertFailure,
                                               testCase)

import           Control.Exception            (ErrorCall (ErrorCall), catch,
                                               evaluate)

import           Data.Kore.AST
import           Data.Kore.FreshVariables.Int


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
                (intVariable objectVariable 1)
                objectVariable { variableName = Id "var1" })
        , testCase "Testing freshVariable Object 2."
            (assertEqual ""
                (runFreshVariables (freshVariable objectVariable) 2)
                (objectVariable { variableName = Id "var2" }, 3))
        , testCase "Testing intVariable Meta 1."
            (assertEqual ""
                (intVariable metaVariable 1)
                metaVariable { variableName = Id "#var1" })
        , testCase "Testing freshVariable Meta 2."
            (assertEqual ""
                (runFreshVariables (freshVariable metaVariable) 2)
                (metaVariable { variableName = Id "#var2" }, 3))
        , testCase "Testing freshVariable Functor Meta 1."
            (assertEqual ""
                (runFreshVariables
                    ((,)
                        <$> freshVariable metaVariable
                        <*> freshVariable metaVariable
                    ) 1)
                (( metaVariable { variableName = Id "#var1" }
                 , metaVariable { variableName = Id "#var2" }), 3))
        , testCase "Testing freshUnifiedVariable Meta 2."
            (assertEqual ""
                (runFreshVariables
                    (freshUnifiedVariable unifiedMetaVariable) 2)
                (MetaVariable $ metaVariable { variableName = Id "#var2" }, 3))
        , testCase "Testing failing freshVariableSuchThat Meta 1."
            ((evaluate (runFreshVariables
                    (freshVariableSuchThat
                        unifiedMetaVariable
                        (== unifiedMetaVariable)
                    ) 2) >> assertFailure "This evaluation should fail")
                `catch` \ (ErrorCall s) ->
                        assertEqual "" s
                            "Cannot generate variable satisfying predicate"
            )
        , testCase "Testing failing freshVariableSuchThat Meta 1."
            (assertEqual ""
                (runFreshVariables
                    (freshVariableSuchThat
                        unifiedMetaVariable
                        (const True)
                    ) 2)
                (MetaVariable $ metaVariable { variableName = Id "#var2" }, 3))
           ]
