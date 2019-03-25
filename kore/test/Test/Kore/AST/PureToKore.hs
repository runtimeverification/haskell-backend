module Test.Kore.AST.PureToKore (test_pureToKore) where

import           Hedgehog
                 ( MonadTest, (===) )
import qualified Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Test.Tasty.HUnit

import           Kore.AST.Kore
import           Kore.AST.Pure as Pure
import           Kore.AST.PureToKore
import           Kore.AST.Sentence
import qualified Kore.Domain.Builtin as Domain
import           Kore.MetaML.AST

import Test.Kore


pureToKoreToPureProp :: MonadTest m => CommonMetaPattern -> m ()
pureToKoreToPureProp p =
    p === patternKoreToPure (patternPureToKore p)

test_pureToKore :: [TestTree]
test_pureToKore =
    [ testProperty "Pattern" $ Hedgehog.property $ do
        metaPattern <-
            Hedgehog.forAll
            $ standaloneGen (metaMLPatternGen =<< sortGen)
        pureToKoreToPureProp (Pure.eraseAnnotations metaPattern)
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
                    :: Definition
                        (Sentence
                            Meta
                            (SortVariable Meta)
                            (ParsedPurePattern Meta Domain.Builtin)
                        )
                )
            )
        )
    ]
