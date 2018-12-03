module Test.Kore.AST.PureToKore (test_pureToKore) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )
import Test.Tasty.QuickCheck
       ( forAll, testProperty )

import           Kore.AST.Kore
import           Kore.AST.PureToKore
import           Kore.AST.Sentence
import qualified Kore.Domain.Builtin as Domain
import           Kore.MetaML.AST

import Test.Kore


pureToKoreToPureProp :: CommonMetaPattern -> Bool
pureToKoreToPureProp p = Right p == patternKoreToPure Meta (patternPureToKore p)

test_pureToKore :: [TestTree]
test_pureToKore =
    [ testProperty "Pattern"
        (forAll metaMLPatternGen pureToKoreToPureProp)
    , testCase "definitionMetaToKore"
        (assertEqual ""
            Definition
                { definitionAttributes = Attributes []
                , definitionModules =
                    [ Module
                        { moduleAttributes = Attributes []
                        , moduleName = ModuleName "TEST-MODULE"
                        , moduleSentences =
                            [ asSentence
                                (SentenceImport
                                    { sentenceImportModuleName =
                                        ModuleName "TEST-MODULE"
                                    , sentenceImportAttributes = Attributes
                                        [ asCommonKorePattern
                                            ( TopPattern Top
                                                { topSort =
                                                    SortVariableSort
                                                        (SortVariable
                                                            (testId "#s1"
                                                            :: Id Meta
                                                            )
                                                        )
                                                }
                                            )
                                        ]
                                    }
                                :: KoreSentenceImport
                                )
                            ]
                        }

                    ]
                }
            (definitionPureToKore
                (Definition
                    { definitionAttributes = Attributes []
                    , definitionModules =
                        [ Module
                            { moduleAttributes = Attributes []
                            , moduleName = ModuleName "TEST-MODULE"
                            , moduleSentences =
                                [ SentenceImportSentence SentenceImport
                                    { sentenceImportModuleName =
                                        ModuleName "TEST-MODULE"
                                    , sentenceImportAttributes = Attributes
                                        [ asCommonKorePattern
                                            ( TopPattern Top
                                                { topSort =
                                                    SortVariableSort
                                                        (SortVariable
                                                            (testId "#s1")
                                                        )
                                                    :: Sort Meta
                                                }
                                            )
                                        ]
                                    }
                                ]
                            }
                        ]
                    }
                  :: PureDefinition Meta Domain.Builtin
                )
            )
        )
    ]
