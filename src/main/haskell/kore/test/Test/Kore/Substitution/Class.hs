{-# OPTIONS_GHC -fno-warn-orphans #-}
module Test.Kore.Substitution.Class (test_class) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import Test.Kore
import Test.Kore.Comparators ()
import Test.Kore.Substitution
import Test.Tasty.HUnit.Extensions

import qualified Data.Text as Text

import           Kore.AST.Kore
import           Kore.Substitution.Class
import qualified Kore.Substitution.List as S
import           Kore.Variables.Fresh

type UnifiedPatternSubstitution =
    S.Substitution (Unified Variable) CommonKorePattern

testSubstitute
    :: CommonKorePattern
    -> UnifiedPatternSubstitution
    -> Counter CommonKorePattern
testSubstitute = substitute

test_class :: [TestTree]
test_class =
    [ testCase "Testing substituting a variable."
        (assertEqualWithExplanation ""
            (objectTopPattern, 2)
            (runCounter
                (testSubstitute objectVariableUnifiedPattern substitution1)
                2
            )
        )
    , testCase "Testing not substituting a variable."
        (assertEqualWithExplanation ""
            (metaVariableUnifiedPattern, 2)
            (runCounter
                (testSubstitute metaVariableUnifiedPattern substitution1)
                2
            )
        )
    , testCase "Testing not substituting anything."
        (assertEqualWithExplanation ""
            (objectBottomPattern, 2)
            (runCounter
                (testSubstitute objectBottomPattern substitution1)
                2
            )
        )
      , testCase "Testing exists => empty substitution."
        (assertEqualWithExplanation ""
            (existsObjectUnifiedPattern1, 2)
            (runCounter
                (testSubstitute existsObjectUnifiedPattern1 substitution1)
                2
            )
        )
      , testCase "Testing forall."
        (assertEqualWithExplanation ""
            (forallObjectUnifiedPattern2, 2)
            (runCounter
                (testSubstitute forallObjectUnifiedPattern1 substitution1)
                2
            )
        )
      , testCase "Testing binder renaming"
        (assertEqualWithExplanation ""
            (existsObjectUnifiedPattern1S 2, 3)
            (runCounter
                (testSubstitute existsObjectUnifiedPattern1 substitution2)
                2
            )
        )
      , testCase "Testing binder renaming and substitution"
        (assertEqualWithExplanation ""
            (forallObjectUnifiedPattern1S3, 6)
            (runCounter
                (testSubstitute forallObjectUnifiedPattern1 substitution3)
                5
            )
        )
      , testCase "Testing double binder renaming"
        (assertEqualWithExplanation ""
            (forallExistsObjectUnifiedPattern1S2, 9)
            (runCounter
                (testSubstitute
                    forallExistsObjectUnifiedPattern1 substitution2)
                7
            )
        )
        , testCase "Testing double binder renaming 1"
        (assertEqualWithExplanation ""
            (forallExistsObjectUnifiedPattern2, 17)
            (runCounter
                (testSubstitute
                    forallExistsObjectUnifiedPattern2 substitution1)
                17
            )
        )
        , testCase "Testing substitution state 1"
        (assertEqualWithExplanation ""
            (testSubstitutionStatePatternS3, 18)
            (runCounter
                (testSubstitute
                    testSubstitutionStatePattern substitution3)
                17
            )
        )
        ]

metaVariableSubstitute :: Int -> Variable Meta
metaVariableSubstitute n =
    metaVariable
        { variableName = Id
            { getId = "#" <> freshVariablePrefix <> Text.pack ("v_" ++ show n)
            , idLocation = AstLocationGeneratedVariable
            }
        }

metaVariableUnifiedPatternSubstitute :: Int -> CommonKorePattern
metaVariableUnifiedPatternSubstitute =
    asCommonKorePattern . VariablePattern . metaVariableSubstitute

objectVariableSubstitute :: Int -> Variable Object
objectVariableSubstitute n =
    objectVariable
        { variableName = Id
            { getId = freshVariablePrefix <> Text.pack ("v_" ++ show n)
            , idLocation = AstLocationGeneratedVariable
            }
        }

objectVariableUnifiedPatternSubstitute :: Int -> CommonKorePattern
objectVariableUnifiedPatternSubstitute =
    asCommonKorePattern . VariablePattern . objectVariableSubstitute

substitution1 :: UnifiedPatternSubstitution
substitution1 = S.fromList
  [ (unifiedObjectVariable, objectTopPattern) ]

substitution2 :: UnifiedPatternSubstitution
substitution2 = S.fromList
  [ (unifiedMetaVariable, objectVariableUnifiedPattern) ]

substitution3 :: UnifiedPatternSubstitution
substitution3 = S.fromList
  [ (unifiedObjectVariable, metaVariableUnifiedPattern) ]

existsObjectUnifiedPattern1 :: CommonKorePattern
existsObjectUnifiedPattern1 = asCommonKorePattern $ ExistsPattern Exists
    { existsSort = objectSort
    , existsVariable = objectVariable
    , existsChild = objectVariableUnifiedPattern
    }

existsMetaUnifiedPattern1 :: CommonKorePattern
existsMetaUnifiedPattern1 = asCommonKorePattern $ ExistsPattern Exists
    { existsSort = metaSort
    , existsVariable = metaVariable
    , existsChild = metaVariableUnifiedPattern
    }

existsMetaUnifiedPattern1S3 :: CommonKorePattern
existsMetaUnifiedPattern1S3 = asCommonKorePattern $ ExistsPattern Exists
    { existsSort = metaSort
    , existsVariable = metaVariableSubstitute 17
    , existsChild = metaVariableUnifiedPatternSubstitute 17
    }

existsObjectUnifiedPattern1S :: Int -> CommonKorePattern
existsObjectUnifiedPattern1S n = asCommonKorePattern $ ExistsPattern Exists
    { existsSort = objectSort
    , existsVariable = objectVariableSubstitute n
    , existsChild = objectVariableUnifiedPatternSubstitute n
    }

forallObjectUnifiedPattern1 :: CommonKorePattern
forallObjectUnifiedPattern1 = asCommonKorePattern $ ForallPattern Forall
    { forallSort = metaSort
    , forallVariable = metaVariable
    , forallChild = objectVariableUnifiedPattern
    }

forallObjectUnifiedPattern2 :: CommonKorePattern
forallObjectUnifiedPattern2 = asCommonKorePattern $ ForallPattern Forall
    { forallSort = metaSort
    , forallVariable = metaVariable
    , forallChild = objectTopPattern
    }

forallObjectUnifiedPattern1S3 :: CommonKorePattern
forallObjectUnifiedPattern1S3 = asCommonKorePattern $ ForallPattern Forall
    { forallSort = metaSort
    , forallVariable = metaVariableSubstitute 5
    , forallChild = metaVariableUnifiedPattern
    }

forallExistsObjectUnifiedPattern1 :: CommonKorePattern
forallExistsObjectUnifiedPattern1 = asCommonKorePattern $ ForallPattern Forall
    { forallSort = objectSort
    , forallVariable = objectVariable
    , forallChild = existsObjectUnifiedPattern1
    }

forallExistsObjectUnifiedPattern2 :: CommonKorePattern
forallExistsObjectUnifiedPattern2 = asCommonKorePattern $ ForallPattern Forall
    { forallSort = metaSort
    , forallVariable = metaVariable
    , forallChild = existsObjectUnifiedPattern1
    }

forallExistsObjectUnifiedPattern1S2 :: CommonKorePattern
forallExistsObjectUnifiedPattern1S2 = asCommonKorePattern $ ForallPattern Forall
    { forallSort = objectSort
    , forallVariable = objectVariableSubstitute 7
    , forallChild = existsObjectUnifiedPattern1S 8
    }

testSubstitutionStatePattern :: CommonKorePattern
testSubstitutionStatePattern =
    asCommonKorePattern $ ApplicationPattern Application
        { applicationSymbolOrAlias = SymbolOrAlias
            { symbolOrAliasConstructor = testId "sigma" :: Id Object
            , symbolOrAliasParams = []
            }
        , applicationChildren =
            [ existsObjectUnifiedPattern1
            , objectVariableUnifiedPattern
            , existsMetaUnifiedPattern1
            , metaVariableUnifiedPattern
            ]
        }

testSubstitutionStatePatternS3 :: CommonKorePattern
testSubstitutionStatePatternS3 =
    asCommonKorePattern $ ApplicationPattern Application
        { applicationSymbolOrAlias = SymbolOrAlias
            { symbolOrAliasConstructor = testId "sigma" :: Id Object
            , symbolOrAliasParams = []
            }
        , applicationChildren =
            [ existsObjectUnifiedPattern1
            , metaVariableUnifiedPattern
            , existsMetaUnifiedPattern1S3
            , metaVariableUnifiedPattern
            ]
        }
