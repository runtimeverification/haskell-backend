module Data.Kore.Substitution.ListTest where

import           Test.Tasty                        (TestTree, testGroup)
import           Test.Tasty.HUnit                  (assertEqual, testCase)

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.Substitution.List

import           Data.Kore.Substitution.TestCommon

type UnifiedPatternSubstitution =
    Substitution (Unified Variable) CommonKorePattern

substitution1 :: UnifiedPatternSubstitution
substitution1 = fromList
  [ (unifiedObjectVariable, objectTopPattern) ]

substitution2 :: UnifiedPatternSubstitution
substitution2 = fromList
  [ (unifiedObjectVariable, objectTopPattern)
  , (unifiedObjectVariable, objectBottomPattern)
  ]

substitutionListTests :: TestTree
substitutionListTests =
    testGroup
        "Substitution.List Tests"
        [ testCase "Testing fromList & toList."
            (assertEqual ""
                [ ( unifiedObjectVariable , objectTopPattern) ]
                (toList substitution2)
            )
        , testCase "Add binding 1"
            (assertEqual ""
                [ (unifiedMetaVariable, objectBottomPattern)
                , (unifiedObjectVariable, objectTopPattern)]
                (toList $ insert
                    unifiedMetaVariable objectBottomPattern substitution1)
            )
         , testCase "Add binding 2"
            (assertEqual ""
                [ (unifiedObjectVariable, objectBottomPattern) ]
                (toList $ insert
                    unifiedObjectVariable objectBottomPattern substitution1)
            )
         , testCase "Remove binding"
            (assertEqual ""
                []
                (toList $ delete unifiedObjectVariable substitution1)
            )
        ]
