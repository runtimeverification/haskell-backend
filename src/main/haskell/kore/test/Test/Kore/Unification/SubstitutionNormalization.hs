module Test.Kore.Unification.SubstitutionNormalization
    (test_substitutionNormalization) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Control.Monad.Except
                 ( runExceptT )
import qualified Data.Set as Set

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.Pattern
                 ( StepPattern )
import           Kore.Step.StepperAttributes
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
import qualified Kore.Unification.Substitution as Substitution
import           Kore.Unification.SubstitutionNormalization
import           Kore.Variables.Fresh

import           Test.Kore
import           Test.Kore.Comparators ()
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions

test_substitutionNormalization :: [TestTree]
test_substitutionNormalization =
    [ testCase "Empty substitution"
        (assertEqual ""
            (Right [])
            (runNormalizeSubstitution
                ([] :: [(Variable Meta, StepPattern Meta Variable)])
            )
        )
    , testCase "Simple substitution"
        (assertEqual ""
            (Right [(v1 patternMetaSort, mkTop_)])
            (runNormalizeSubstitution
                [(v1 patternMetaSort, mkTop_)]
            )
        )
    , testCase "Simple unnormalized substitution"
        (assertEqual ""
            (Right
                [ (v1 patternMetaSort, mkTop patternMetaSort)
                , (x1 patternMetaSort, mkTop patternMetaSort)
                ]
            )
            (runNormalizeSubstitution
                [ (v1 patternMetaSort, mkVar $ x1 patternMetaSort)
                , (x1 patternMetaSort, mkTop patternMetaSort)
                ]
            )
        )
    , testCase "Unnormalized substitution with 'and'"
        (assertEqual ""
            (Right
                [   ( v1 patternMetaSort
                    , mkAnd mkTop_ (mkTop patternMetaSort)
                    )
                , (x1 patternMetaSort, mkTop patternMetaSort)
                ]
            )
            (runNormalizeSubstitution
                [   ( v1 patternMetaSort
                    , mkAnd (mkVar $ x1 patternMetaSort) mkTop_
                    )
                ,   (x1 patternMetaSort, mkTop patternMetaSort)
                ]
            )
        )
    , let
        var1 =  (v1 patternMetaSort)
      in
        testCase "Simplest cycle"
            (assertEqual ""
                (Right [])
                (runNormalizeSubstitution [(var1, mkVar $ v1 patternMetaSort)])
            )
    , let
        var1 =  (v1 patternMetaSort)
        varx1 =  (x1 patternMetaSort)
      in
        testCase "Cycle with extra substitution"
            (assertEqual ""
                (Right [(x1 patternMetaSort, mkVar $ v1 patternMetaSort)])
                (runNormalizeSubstitution
                    [ (var1, mkVar $ v1 patternMetaSort)
                    , (varx1, mkVar $ v1 patternMetaSort)
                    ]
                )
            )
    , let
        var1 =  (v1 patternMetaSort)
      in
        testCase "Function cycle"
            (assertEqual ""
                (Left (NonCtorCircularVariableDependency [var1]))
                (runNormalizeSubstitution
                    [   ( var1
                        , mkApp patternMetaSort f [mkVar var1]
                        )
                    ]
                )
            )
    , let
        var1 =  (v1 patternMetaSort)
        varx1 =  (x1 patternMetaSort)
      in
        testCase "Length 2 cycle"
            (assertEqual ""
                (Right [])
                (runNormalizeSubstitution
                    [ (var1, mkVar $ x1 patternMetaSort)
                    , (varx1, mkVar $ v1 patternMetaSort)
                    ]
                )
            )
    , let
        var1 =  (v1 patternMetaSort)
        varx1 =  (x1 patternMetaSort)
      in
        testCase "Cycle with 'and'"
            (assertEqual ""
                (Right [])
                (runNormalizeSubstitution
                    [ (var1, mkAnd (mkVar $ x1 patternMetaSort) mkTop_)
                    , (varx1, mkAnd (mkVar $ v1 patternMetaSort) mkTop_)
                    ]
                )
            )
    , let
        var1 =  (v1 patternMetaSort)
        varx1 =  (x1 patternMetaSort)
      in
        testCase "Length 2 non-ctor cycle"
            (assertEqual ""
                (Left (NonCtorCircularVariableDependency [var1, varx1]))
                (runNormalizeSubstitution
                    [ (var1, mkApp patternMetaSort f [mkVar varx1])
                    , (varx1, mkVar var1)
                    ]
                )
            )
    , testCase "Constructor cycle"
        (assertEqualWithExplanation ""
            (Right [])
            (runNormalizeSubstitutionObject
                [ (Mock.x, Mock.constr10 (mkVar Mock.x))
                ]
            )
        )
    , testCase "Constructor with side function cycle"
        (assertEqualWithExplanation ""
            (Right [])
            (runNormalizeSubstitutionObject
                [ (Mock.x, Mock.constr20 (Mock.f (mkVar Mock.x)) (mkVar Mock.x))
                ]
            )
        )
    , testCase "Constructor with function cycle"
        (assertEqualWithExplanation ""
            (Left (NonCtorCircularVariableDependency [Mock.x]))
            (runNormalizeSubstitutionObject
                [ (Mock.x, Mock.constr10 (Mock.f (mkVar Mock.x)))
                ]
            )
        )
    ]
  where
    v1 :: Sort level -> Variable level
    v1 = Variable (testId "v1")
    x1 :: Sort level -> Variable level
    x1 = Variable (testId "x1")
    f = groundHead "f" AstLocationTest

runNormalizeSubstitution
    :: MetaOrObject level
    => [(Variable level, StepPattern level Variable)]
    -> Either
        (SubstitutionError level Variable)
        [(Variable level, StepPattern level Variable)]
runNormalizeSubstitution substitution =
    fmap (Substitution.unwrap . Predicated.substitution)
    . evalCounter
    . runExceptT
    $ normalizeSubstitution mockMetadataTools (Substitution.wrap substitution)

runNormalizeSubstitutionObject
    :: [(Variable Object, StepPattern Object Variable)]
    -> Either
        (SubstitutionError Object Variable)
        [(Variable Object, StepPattern Object Variable)]
runNormalizeSubstitutionObject substitution =
    fmap (Substitution.unwrap . Predicated.substitution)
    . evalCounter
    . runExceptT
    $ normalizeSubstitution mockMetadataToolsO (Substitution.wrap substitution)
  where
    mockMetadataToolsO :: MetadataTools Object StepperAttributes
    mockMetadataToolsO =
        Mock.makeMetadataTools
            Mock.attributesMapping
            Mock.headTypeMapping
            Mock.sortAttributesMapping
            Mock.subsorts

mockMetadataTools :: MetaOrObject level => MetadataTools level StepperAttributes
mockMetadataTools = MetadataTools
    { symAttributes = const Mock.functionalAttributes
    , symbolOrAliasType = const HeadType.Symbol
    , sortAttributes = const Mock.functionalAttributes
    , isSubsortOf = const $ const False
    , subsorts = Set.singleton
    }
