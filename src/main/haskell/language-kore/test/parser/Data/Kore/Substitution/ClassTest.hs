{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances  #-}
module Data.Kore.Substitution.ClassTest where

import           Test.Tasty                        (TestTree, testGroup)
import           Test.Tasty.HUnit                  (assertEqual, testCase)

import           Data.Kore.AST
import           Data.Kore.FreshVariables.Int
import           Data.Kore.Substitution.Class
import           Data.Kore.Substitution.List       as S

import           Data.Kore.Substitution.TestCommon

type UnifiedPatternSubstitution =
    S.Substitution (UnifiedVariable Variable) UnifiedPattern

instance PatternSubstitutionClass Variable UnifiedPatternSubstitution FreshVariables where

testSubstitute
    :: UnifiedPattern
    -> UnifiedPatternSubstitution
    -> FreshVariables UnifiedPattern
testSubstitute = substitute

substitutionClassTests :: TestTree
substitutionClassTests =
    testGroup
        "Substitution.List Tests"
        [ testCase "Testing substituting a variable."
            (assertEqual ""
                (objectTopPattern, 2)
                (runFreshVariables
                    (testSubstitute objectVariableUnifiedPattern substitution1)
                    2
                )
            )
        , testCase "Testing not substituting a variable."
            (assertEqual ""
                (metaVariableUnifiedPattern, 2)
                (runFreshVariables
                    (testSubstitute metaVariableUnifiedPattern substitution1)
                    2
                )
            )
        , testCase "Testing not substituting anything."
            (assertEqual ""
                (objectBottomPattern, 2)
                (runFreshVariables
                    (testSubstitute objectBottomPattern substitution1)
                    2
                )
            )
         , testCase "Testing exists => empty substitution."
            (assertEqual ""
                (existsObjectUnifiedPattern1, 2)
                (runFreshVariables
                    (testSubstitute existsObjectUnifiedPattern1 substitution1)
                    2
                )
            )
         , testCase "Testing forall."
            (assertEqual ""
                (forallObjectUnifiedPattern2, 2)
                (runFreshVariables
                    (testSubstitute forallObjectUnifiedPattern1 substitution1)
                    2
                )
            )
         , testCase "Testing binder renaming"
            (assertEqual ""
                (existsObjectUnifiedPattern1S 2, 3)
                (runFreshVariables
                    (testSubstitute existsObjectUnifiedPattern1 substitution2)
                    2
                )
            )
          , testCase "Testing binder renaming and substitution"
            (assertEqual ""
                (forallObjectUnifiedPattern1S3, 6)
                (runFreshVariables
                    (testSubstitute forallObjectUnifiedPattern1 substitution3)
                    5
                )
            )
          , testCase "Testing double binder renaming"
            (assertEqual ""
                (forallExistsObjectUnifiedPattern1S2, 9)
                (runFreshVariables
                    (testSubstitute
                        forallExistsObjectUnifiedPattern1 substitution2)
                    7
                )
            )
          ]

metaVariableSubstitute :: Int -> Variable Meta
metaVariableSubstitute = intVariable metaVariable

objectVariableSubstitute :: Int -> Variable Object
objectVariableSubstitute = intVariable objectVariable

objectVariableUnifiedPatternSubstitute :: Int -> UnifiedPattern
objectVariableUnifiedPatternSubstitute =
    ObjectPattern . VariablePattern . objectVariableSubstitute

substitution1 :: UnifiedPatternSubstitution
substitution1 = fromList
  [ (unifiedObjectVariable, objectTopPattern) ]

substitution2 :: UnifiedPatternSubstitution
substitution2 = fromList
  [ (unifiedMetaVariable, objectVariableUnifiedPattern) ]

substitution3 :: UnifiedPatternSubstitution
substitution3 = fromList
  [ (unifiedObjectVariable, metaVariableUnifiedPattern) ]

existsObjectUnifiedPattern1 :: UnifiedPattern
existsObjectUnifiedPattern1 = ObjectPattern $ ExistsPattern Exists
    { existsSort = objectSort
    , existsVariable = unifiedObjectVariable
    , existsPattern = objectVariableUnifiedPattern
    }

existsObjectUnifiedPattern1S :: Int -> UnifiedPattern
existsObjectUnifiedPattern1S n = ObjectPattern $ ExistsPattern Exists
    { existsSort = objectSort
    , existsVariable = ObjectVariable $ objectVariableSubstitute n
    , existsPattern = objectVariableUnifiedPatternSubstitute n
    }

forallObjectUnifiedPattern1 :: UnifiedPattern
forallObjectUnifiedPattern1 = ObjectPattern $ ForallPattern Forall
    { forallSort = objectSort
    , forallVariable = unifiedMetaVariable
    , forallPattern = objectVariableUnifiedPattern
    }

forallObjectUnifiedPattern2 :: UnifiedPattern
forallObjectUnifiedPattern2 = ObjectPattern $ ForallPattern Forall
    { forallSort = objectSort
    , forallVariable = unifiedMetaVariable
    , forallPattern = objectTopPattern
    }

forallObjectUnifiedPattern1S3 :: UnifiedPattern
forallObjectUnifiedPattern1S3 = ObjectPattern $ ForallPattern Forall
    { forallSort = objectSort
    , forallVariable = MetaVariable $ metaVariableSubstitute 5
    , forallPattern = metaVariableUnifiedPattern
    }

forallExistsObjectUnifiedPattern1 :: UnifiedPattern
forallExistsObjectUnifiedPattern1 = ObjectPattern $ ForallPattern Forall
    { forallSort = objectSort
    , forallVariable = unifiedObjectVariable
    , forallPattern = existsObjectUnifiedPattern1
    }

forallExistsObjectUnifiedPattern1S2 :: UnifiedPattern
forallExistsObjectUnifiedPattern1S2 = ObjectPattern $ ForallPattern Forall
    { forallSort = objectSort
    , forallVariable = ObjectVariable $ objectVariableSubstitute 7
    , forallPattern = existsObjectUnifiedPattern1S 8
    }


