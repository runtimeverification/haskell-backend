module Test.Kore.Unification.SubstitutionNormalization
    (test_substitutionNormalization) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import Data.Default
       ( def )

import           Kore.AST.Common
                 ( AstLocation (..), Sort (..), SortVariable (..), Variable,
                 noLocationId )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( CommonPurePattern, groundHead )
import           Kore.AST.PureToKore
                 ( patternKoreToPure )
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTUtils.SmartPatterns
import           Kore.Building.AsAst
import           Kore.Building.Patterns
import           Kore.Building.Sorts
import           Kore.Error
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SortTools )
import           Kore.MetaML.AST
                 ( CommonMetaPattern )
import qualified Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import           Kore.Step.StepperAttributes
import           Kore.Unification.Error
                 ( SubstitutionError (..) )
import           Kore.Unification.SubstitutionNormalization
import           Kore.Unification.UnifierImpl
                 ( UnificationSubstitution )
import           Kore.Variables.Fresh.IntCounter
                 ( runIntCounter )

test_substitutionNormalization :: [TestTree]
test_substitutionNormalization =
    [ testCase "Empty substitution"
        (assertEqual ""
            (Right [])
            (runNormalizeSubstitution
                ([] :: [(Variable Meta, CommonPurePattern Meta)])
            )
        )
    , testCase "Simple substitution"
        (assertEqual ""
            (Right
                [   ( asVariable (v1 PatternSort)
                    , asPureMetaPattern (metaTop PatternSort)
                    )
                ]
            )
            (runNormalizeSubstitution
                [   ( asVariable (v1 PatternSort)
                    , asPureMetaPattern (metaTop PatternSort)
                    )
                ]
            )
        )
    , testCase "Simple unnormalized substitution"
        (assertEqual ""
            (Right
                [   ( asVariable (v1 PatternSort)
                    , asPureMetaPattern (metaTop PatternSort)
                    )
                ,   ( asVariable (x1 PatternSort)
                    , asPureMetaPattern (metaTop PatternSort)
                    )
                ]
            )
            (runNormalizeSubstitution
                [   ( asVariable (v1 PatternSort)
                    , asPureMetaPattern (x1 PatternSort)
                    )
                ,   ( asVariable (x1 PatternSort)
                    , asPureMetaPattern (metaTop PatternSort)
                    )
                ]
            )
        )
    , testCase "Unnormalized substitution with 'and'"
        (assertEqual ""
            (Right
                [   ( asVariable (v1 PatternSort)
                    , asPureMetaPattern
                        ( metaAnd
                            PatternSort
                            (metaTop PatternSort)
                            (metaTop PatternSort)
                        )
                    )
                ,   ( asVariable (x1 PatternSort)
                    , asPureMetaPattern (metaTop PatternSort)
                    )
                ]
            )
            (runNormalizeSubstitution
                [   ( asVariable (v1 PatternSort)
                    , asPureMetaPattern
                        ( metaAnd
                            PatternSort
                            (x1 PatternSort)
                            (metaTop PatternSort)
                        )
                    )
                ,   ( asVariable (x1 PatternSort)
                    , asPureMetaPattern (metaTop PatternSort)
                    )
                ]
            )
        )
    , let
        var1 = asVariable (v1 PatternSort)
      in
        testCase "Simplest cycle"
            (assertEqual ""
                (Left (CtorCircularVariableDependency [var1]))
                (runNormalizeSubstitution
                    [   ( var1
                        , asPureMetaPattern (v1 PatternSort)
                        )
                    ]
                )
            )
    , let
        var1 = asVariable (v1 PatternSort)
        varx1 = asVariable (x1 PatternSort)
      in
        testCase "Length 2 cycle"
            (assertEqual ""
                (Left (CtorCircularVariableDependency [var1, varx1]))
                (runNormalizeSubstitution
                    [   ( var1
                        , asPureMetaPattern (x1 PatternSort)
                        )
                    ,   ( varx1
                        , asPureMetaPattern (v1 PatternSort)
                        )
                    ]
                )
            )
    , let
        var1 = asVariable (v1 PatternSort)
        varx1 = asVariable (x1 PatternSort)
      in
        testCase "Cycle with 'and'"
            (assertEqual ""
                (Left (CtorCircularVariableDependency [var1, varx1]))
                (runNormalizeSubstitution
                    [   ( var1
                        , asPureMetaPattern
                            ( metaAnd
                                PatternSort
                                (x1 PatternSort)
                                (metaTop PatternSort)
                            )
                        )
                    ,   ( varx1
                        , asPureMetaPattern
                            ( metaAnd
                                PatternSort
                                (v1 PatternSort)
                                (metaTop PatternSort)
                            )
                        )
                    ]
                )
            )
    , let
        var1 = asVariable (v1 PatternSort)
        varx1 = asVariable (x1 PatternSort)
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
    v1 :: MetaSort sort => sort -> MetaVariable sort
    v1 = metaVariable "v1" AstLocationTest
    x1 :: MetaSort sort => sort -> MetaVariable sort
    x1 = metaVariable "x1" AstLocationTest
    f = groundHead "f" AstLocationTest
    asPureMetaPattern
        :: ProperPattern level sort patt => patt -> CommonMetaPattern
    asPureMetaPattern patt =
        case patternKoreToPure Meta (asAst patt) of
            Left err  -> error (printError err)
            Right pat -> pat

runNormalizeSubstitution
    :: MetaOrObject level
    => UnificationSubstitution level Variable
    -> Either
        (SubstitutionError level Variable)
        (UnificationSubstitution level Variable)
runNormalizeSubstitution substitution =
    case normalizeSubstitution mockMetadataTools substitution of
        Left err     -> Left err
        Right action -> Right $ PredicateSubstitution.substitution
                        $ fst $ runIntCounter action 0

mockStepperAttributes :: StepperAttributes
mockStepperAttributes = StepperAttributes
    { isConstructor = False
    , isFunctional = True
    , isFunction = False
    , hook = def
    }

mockSortTools :: MetaOrObject level => SortTools level
mockSortTools = const ApplicationSorts
    { applicationSortsOperands = []
    , applicationSortsResult   =
        SortVariableSort SortVariable
            { getSortVariable = noLocationId "S" }
    }

mockMetadataTools :: MetaOrObject level => MetadataTools level StepperAttributes
mockMetadataTools = MetadataTools
    { attributes = const mockStepperAttributes
    , sortTools = mockSortTools
    }

