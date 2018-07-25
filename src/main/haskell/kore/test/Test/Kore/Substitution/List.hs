module Test.Kore.Substitution.List (test_list) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import Test.Kore.Substitution

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.Substitution.List

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

test_list :: [TestTree]
test_list =
    [ testCase "Testing fromList & toList"
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
