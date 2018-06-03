module Data.Kore.Variables.SortTest (freeSortVariablesTests) where

import           Test.Tasty                  (TestTree, testGroup)
import           Test.Tasty.HUnit            (assertEqual, testCase)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Sentence
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.Building.AsAst
import           Data.Kore.Building.Patterns
import           Data.Kore.Building.Sorts    as Sorts
import           Data.Kore.Variables.Sort

import qualified Data.Set                    as Set

freeSortVariablesTests :: TestTree
freeSortVariablesTests =
    testGroup "Tests for free variable identification"
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
