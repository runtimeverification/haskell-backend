module Test.Kore.Unification.SubstitutionNormalization
    (test_substitutionNormalization) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Control.Monad.Except
                 ( runExceptT )
import           Data.Reflection
                 ( give )
import qualified Data.Set as Set

import           Kore.AST.Pure
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartConstructors
import           Kore.ASTUtils.SmartPatterns
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SymbolOrAliasSorts )
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
import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock

test_substitutionNormalization :: [TestTree]
test_substitutionNormalization =
    give (mockSymbolOrAliasSorts :: SymbolOrAliasSorts Object)
    $ give (mockSymbolOrAliasSorts :: SymbolOrAliasSorts Meta)
    [ testCase "Empty substitution"
        (assertEqual ""
            (Right [])
            (runNormalizeSubstitution
                ([] :: [(Variable Meta, StepPattern Meta Variable)])
            )
        )
    , testCase "Simple substitution"
        (assertEqual ""
            (Right [(v1 patternMetaSort, mkTop)])
            (runNormalizeSubstitution
                [(v1 patternMetaSort, mkTop)]
            )
        )
    , testCase "Simple unnormalized substitution"
        (assertEqual ""
            (Right
                [ (v1 patternMetaSort, mkTop)
                , (x1 patternMetaSort, mkTop)
                ]
            )
            (runNormalizeSubstitution
                [ (v1 patternMetaSort, mkVar $ x1 patternMetaSort)
                , (x1 patternMetaSort, mkTop)
                ]
            )
        )
    , testCase "Unnormalized substitution with 'and'"
        (assertEqual ""
            (Right
                [   ( v1 patternMetaSort
                    , And_ patternMetaSort mkTop (Top_ patternMetaSort)
                    )
                , (x1 patternMetaSort, mkTop)
                ]
            )
            (runNormalizeSubstitution
                [   ( v1 patternMetaSort
                    , mkAnd (mkVar $ x1 patternMetaSort) mkTop
                    )
                ,   (x1 patternMetaSort, mkTop)
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
                        , mkApp f [mkVar var1]
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
                    [ (var1, mkAnd (mkVar $ x1 patternMetaSort) mkTop)
                    , (varx1, mkAnd (mkVar $ v1 patternMetaSort) mkTop)
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
                    [ (var1, mkApp f [mkVar varx1])
                    , (varx1, mkVar var1)
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

mockSymbolOrAliasSorts :: SymbolOrAliasSorts level
mockSymbolOrAliasSorts = const ApplicationSorts
    { applicationSortsOperands = []
    , applicationSortsResult   =
        SortVariableSort SortVariable
            { getSortVariable = noLocationId "S" }
    }

mockMetadataTools :: MetadataTools level StepperAttributes
mockMetadataTools = MetadataTools
    { symAttributes = const Mock.functionalAttributes
    , symbolOrAliasType = const HeadType.Symbol
    , sortAttributes = const Mock.functionalAttributes
    , symbolOrAliasSorts = mockSymbolOrAliasSorts
    , isSubsortOf = const $ const False
    , subsorts = Set.singleton
    }
