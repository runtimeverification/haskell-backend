module Data.Kore.AST.PureToKoreTest where

import           Test.Tasty                 (TestTree, testGroup)
import           Test.Tasty.HUnit           (assertEqual, testCase)
import           Test.Tasty.QuickCheck      (forAll, testProperty)

import           Data.Fix

import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.AST.PureToKore
import           Data.Kore.KoreHelpers
import           Data.Kore.MetaML.AST
import           Data.Kore.MetaML.ASTGen


pureToKoreToPureProp :: CommonMetaPattern -> Bool
pureToKoreToPureProp p = p == patternKoreToPure Meta (patternPureToKore p)

pureToKoreToPureTests :: TestTree
pureToKoreToPureTests =
    testGroup
        "QuickCheck Pure to Kore to Pure Tests"
        [ testProperty "Pattern"
            (forAll metaMLPatternGen pureToKoreToPureProp)

        ]

pureToKoreTests :: TestTree
pureToKoreTests =
    testGroup
        "PureToKore Tests"
        [ pureToKoreToPureTests
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
                                            [ Fix
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
