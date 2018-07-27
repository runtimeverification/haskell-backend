module Test.Kore.Variables.Sort (test_freeSortVariables) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import qualified Data.Set as Set

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.Building.AsAst
import Kore.Building.Patterns
import Kore.Building.Sorts as Sorts
import Kore.Variables.Sort

test_freeSortVariables :: [TestTree]
test_freeSortVariables =
    [ testCase "identifies variable"
        (assertEqual "Expected to find sort variable"
            (Set.singleton
                (UnifiedMeta
                    (asMetaSortVariable
                        (MetaSortVariable1 "#s" AstLocationTest)))
            )
            (sortVariables
                (asAst
                    (metaVariable
                        "#s"
                        AstLocationTest
                        (MetaSortVariable1 "#s" AstLocationTest)
                    )
                    :: CommonKorePattern
                )
            )
        )
    ]
