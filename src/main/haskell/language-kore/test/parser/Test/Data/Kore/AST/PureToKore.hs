module Test.Data.Kore.AST.PureToKore (test_pureToKore) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )
import Test.Tasty.QuickCheck
       ( forAll, testProperty )

import Test.Data.Kore
import Test.Data.Kore.MetaML.AST

import Data.Kore.AST.Common
import Data.Kore.AST.Kore
import Data.Kore.AST.MetaOrObject
import Data.Kore.AST.PureML
import Data.Kore.AST.PureToKore
import Data.Kore.AST.Sentence
import Data.Kore.MetaML.AST


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
