module Data.Kore.Variables.SortTest (freeSortVariablesTests) where

import           Test.Tasty                  (TestTree, testGroup)
import           Test.Tasty.HUnit            (assertEqual, testCase)

import           Data.Kore.AST.Kore
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
                (MetaSortVariable (asMetaSortVariable (MetaSortVariable1 "#s")))
            )
            (sortVariables
                (asAst
                    (metaVariable "#s" (MetaSortVariable1 "#s"))
                    :: UnifiedPattern
                )
            )
        )
    ]
