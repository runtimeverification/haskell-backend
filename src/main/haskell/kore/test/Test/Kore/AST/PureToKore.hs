module Test.Kore.AST.PureToKore (test_pureToKore) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )
import Test.Tasty.QuickCheck
       ( forAll, testProperty )

import Kore.AST.Common
import Kore.AST.Kore
import Kore.AST.MetaOrObject
import Kore.AST.PureML
import Kore.AST.PureToKore
import Kore.AST.Sentence
import Kore.MetaML.AST

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
                                        [ asKorePattern
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
                                        [ asMetaKorePattern
                                            ( TopPattern Top
                                                { topSort =
                                                    SortVariableSort
                                                        (SortVariable
                                                            (testId "#s1")
                                                        )
                                                }
                                            )
                                        ]
                                    }
                                ]
                            }
                        ]
                    }
                  :: PureDefinition Meta
                )
            )
        )
    ]
