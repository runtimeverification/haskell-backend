module Test.Kore.Unification.SubstitutionNormalization
    (test_substitutionNormalization) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Control.Monad.Except
                 ( runExceptT )
import qualified Data.Set as Set

import qualified Test.Kore.IndexedModule.MockMetadataTools as Mock

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartPatterns
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SymbolOrAliasSorts )
import qualified Kore.IndexedModule.MetadataTools as HeadType
                 ( HeadType (..) )
import qualified Kore.Step.ExpandedPattern as Predicated
import           Kore.Step.StepperAttributes
import           Kore.Unification.Data
                 ( UnificationSubstitution )
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
import           Kore.Unification.SubstitutionNormalization
import           Kore.Variables.Fresh

import Test.Kore

test_substitutionNormalization :: [TestTree]
test_substitutionNormalization =
    [ testCase "Empty substitution"
        (assertEqual ""
            (Right [])
            (runNormalizeSubstitution
                ([] :: UnificationSubstitution Meta Variable)
            )
        )
    , testCase "Simple substitution"
        (assertEqual ""
            (Right [(v1 patternMetaSort, Top_ patternMetaSort)])
            (runNormalizeSubstitution
                [(v1 patternMetaSort , Top_ patternMetaSort)]
            )
        )
    , testCase "Simple unnormalized substitution"
        (assertEqual ""
            (Right
                [ (v1 patternMetaSort, Top_ patternMetaSort)
                , (x1 patternMetaSort, Top_ patternMetaSort)
                ]
            )
            (runNormalizeSubstitution
                [ (v1 patternMetaSort, Var_ $ x1 patternMetaSort)
                , (x1 patternMetaSort, Top_ patternMetaSort)
                ]
            )
        )
    , testCase "Unnormalized substitution with 'and'"
        (assertEqual ""
            (Right
                [   ( v1 patternMetaSort
                    ,
                        ( And_
                            patternMetaSort
                            (Top_ patternMetaSort)
                            (Top_ patternMetaSort)
                        )
                    )
                ,   (  (x1 patternMetaSort)
                    ,  (Top_ patternMetaSort)
                    )
                ]
            )
            (runNormalizeSubstitution
                [   (  (v1 patternMetaSort)
                    ,
                        ( And_
                            patternMetaSort
                            (Var_ $ x1 patternMetaSort)
                            (Top_ patternMetaSort)
                        )
                    )
                ,   (  (x1 patternMetaSort)
                    ,  (Top_ patternMetaSort)
                    )
                ]
            )
        )
    , let
        var1 =  (v1 patternMetaSort)
      in
        testCase "Simplest cycle"
            (assertEqual ""
                (Right [])
                (runNormalizeSubstitution
                    [   ( var1
                        , Var_ $ v1 patternMetaSort
                        )
                    ]
                )
            )
    , let
        var1 =  (v1 patternMetaSort)
        varx1 =  (x1 patternMetaSort)
      in
        testCase "Cycle with extra substitution"
            (assertEqual ""
                (Right
                    [   (  (x1 patternMetaSort)
                        ,  Var_ $ v1 patternMetaSort
                        )
                    ]
                )
                (runNormalizeSubstitution
                    [   ( var1
                        ,  Var_ $ v1 patternMetaSort
                        )
                    ,   ( varx1
                        ,  Var_ $ v1 patternMetaSort
                        )
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
                        , App_ f [Var_ var1]
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
                    [   ( var1
                        ,  Var_ $ x1 patternMetaSort
                        )
                    ,   ( varx1
                        ,  Var_ $ v1 patternMetaSort
                        )
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
                    [   ( var1
                        ,
                            ( And_
                                patternMetaSort
                                (Var_ $ x1 patternMetaSort)
                                (Top_ patternMetaSort)
                            )
                        )
                    ,   ( varx1
                        ,
                            ( And_
                                patternMetaSort
                                (Var_ $ v1 patternMetaSort)
                                (Top_ patternMetaSort)
                            )
                        )
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
                    [   ( var1
                        , App_ f [Var_ varx1]
                        )
                    ,   ( varx1
                        , Var_ var1
                        )
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
    => UnificationSubstitution level Variable
    -> Either
        (SubstitutionError level Variable)
        (UnificationSubstitution level Variable)
runNormalizeSubstitution substitution =
    fmap Predicated.substitution
    . evalCounter
    . runExceptT
    $ normalizeSubstitution mockMetadataTools substitution

mockSymbolOrAliasSorts :: MetaOrObject level => SymbolOrAliasSorts level
mockSymbolOrAliasSorts = const ApplicationSorts
    { applicationSortsOperands = []
    , applicationSortsResult   =
        SortVariableSort SortVariable
            { getSortVariable = noLocationId "S" }
    }

mockMetadataTools :: MetaOrObject level => MetadataTools level StepperAttributes
mockMetadataTools = MetadataTools
    { symAttributes = const Mock.functionalAttributes
    , symbolOrAliasType = const HeadType.Symbol
    , sortAttributes = const Mock.functionalAttributes
    , symbolOrAliasSorts = mockSymbolOrAliasSorts
    , isSubsortOf = const $ const False
    , subsorts = Set.singleton
    }
