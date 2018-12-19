module Test.Kore.IndexedModule.Resolvers (test_resolvers) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Data.Default
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )

import           Kore.Annotation.Valid
import           Kore.AST.Kore
import           Kore.AST.Pure
import           Kore.AST.PureToKore
import           Kore.AST.Sentence
import           Kore.AST.Valid
import           Kore.ASTHelpers
import           Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.Resolvers
import           Kore.Step.Pattern

import Test.Kore
import Test.Kore.ASTVerifier.DefinitionVerifier

objectS1 :: Sort Object
objectS1 = simpleSort (SortName "s1")

objectA :: SentenceSymbol Object (CommonStepPattern Object)
objectA = mkSymbol_ (testId "a") [] objectS1

objectB :: SentenceAlias Object (CommonStepPattern Object)
objectB = mkAlias_ (testId "b") objectS1 [] $ mkTop objectS1

metaA :: SentenceSymbol Meta (CommonStepPattern Meta)
metaA = mkSymbol_ (testId "#a") [] charListMetaSort

metaB :: SentenceAlias Meta (CommonStepPattern Meta)
metaB = mkAlias_ (testId "#b") charListMetaSort [] $ mkTop charListMetaSort

testObjectModuleName :: ModuleName
testObjectModuleName = ModuleName "TEST-OBJECT-MODULE"

testMetaModuleName :: ModuleName
testMetaModuleName = ModuleName "TEST-META-MODULE"

testSubMainModuleName :: ModuleName
testSubMainModuleName = ModuleName "TEST-SUB-MAIN-MODULE"

testMainModuleName :: ModuleName
testMainModuleName = ModuleName "TEST-MAIN-MODULE"

strictAttribute :: CommonKorePattern
strictAttribute =
    (asCommonKorePattern . ApplicationPattern)
        Application
            { applicationSymbolOrAlias =
                groundHead "strict" AstLocationTest :: SymbolOrAlias Object
            , applicationChildren = []
            }

testObjectModule :: Module (VerifiedPureSentence Object)
testObjectModule =
    Module
        { moduleName = testObjectModuleName
        , moduleSentences =
            [ SentenceSortSentence
                SentenceSort
                    { sentenceSortName = testId "s1"
                    , sentenceSortParameters = []
                    , sentenceSortAttributes = Attributes [strictAttribute]
                    }
            , asSentence objectA
            , asSentence objectB
            ]
        , moduleAttributes = Attributes [strictAttribute]
        }

testMetaModule :: Module (VerifiedPureSentence Meta)
testMetaModule =
    Module
        { moduleName = testMetaModuleName
        , moduleSentences =
            [ asSentence metaA
            , asSentence metaB
            ]
        , moduleAttributes = Attributes []
        }

subMainModule :: VerifiedKoreModule
subMainModule =
    Module
        { moduleName = testSubMainModuleName
        , moduleSentences =
            [ importSentence testMetaModuleName
            , importSentence testObjectModuleName
            ]
        , moduleAttributes = Attributes [strictAttribute]
        }

mainModule :: VerifiedKoreModule
mainModule =
    Module
        { moduleName = testMainModuleName
        , moduleSentences =
            [ importSentence testMetaModuleName
            , importSentence testSubMainModuleName
            ]
        , moduleAttributes = Attributes []
        }


testDefinition :: VerifiedKoreDefinition
testDefinition =
    Definition
        { definitionAttributes = Attributes [strictAttribute]
        , definitionModules =
            [ modulePureToKore testObjectModule
            , modulePureToKore testMetaModule
            , subMainModule
            , mainModule
            ]
        }

testIndexedModule :: VerifiedModule Attribute.Null Attribute.Null
testIndexedModule =
    case
        verifyAndIndexDefinition
            DoNotVerifyAttributes
            Builtin.koreVerifiers
            (eraseUnifiedSentenceAnnotations <$> testDefinition)
      of
        Right modulesMap ->
            fromMaybe
                (error "This should not have happened")
                (Map.lookup testMainModuleName modulesMap)
        Left err -> error (printError err)

test_resolvers :: [TestTree]
test_resolvers =
    [ testCase "object sort"
        (assertEqual ""
            (Right (def :: Attribute.Null, SentenceSort
                { sentenceSortName = testId "s1"
                , sentenceSortParameters = []
                , sentenceSortAttributes = Attributes [strictAttribute]
                })
            )
            (resolveSort testIndexedModule (testId "s1" :: Id Object))
        )
    , testCase "meta sort"
        (assertEqual ""
            (Right (def :: Attribute.Null, SentenceSort
                { sentenceSortName = charMetaId
                , sentenceSortParameters = []
                , sentenceSortAttributes = Attributes []
                }
            ))
            (resolveSort testIndexedModule charMetaId)
        )
    , testCase "object symbol"
        (assertEqual ""
            (Right (def :: Attribute.Null, SentenceSymbol
                { sentenceSymbolAttributes = Attributes []
                , sentenceSymbolSymbol = sentenceSymbolSymbol objectA
                , sentenceSymbolSorts = []
                , sentenceSymbolResultSort = objectS1
                }
            ))
            (resolveSymbol testIndexedModule (testId "a" :: Id Object))
        )
    , testCase "meta symbol"
        (assertEqual ""
            (Right (def :: Attribute.Null, SentenceSymbol
                { sentenceSymbolAttributes = Attributes []
                , sentenceSymbolSymbol = sentenceSymbolSymbol metaA
                , sentenceSymbolSorts = []
                , sentenceSymbolResultSort = charListMetaSort
                }
            ))
            (resolveSymbol testIndexedModule (testId "#a" :: Id Meta))
        )
    , testCase "object alias"
        (assertEqual ""
            (Right
                ( def :: Attribute.Null
                , SentenceAlias
                    { sentenceAliasAttributes = Attributes []
                    , sentenceAliasAlias = sentenceAliasAlias objectB
                    , sentenceAliasSorts = []
                    , sentenceAliasLeftPattern =
                        Application
                            { applicationSymbolOrAlias =
                                SymbolOrAlias
                                    { symbolOrAliasConstructor =
                                        aliasConstructor
                                            (sentenceAliasAlias objectB)
                                    , symbolOrAliasParams =
                                        (<$>)
                                            SortVariableSort
                                            (aliasParams
                                                $ sentenceAliasAlias objectB
                                            )
                                    }
                            , applicationChildren = []
                            }
                    , sentenceAliasRightPattern =
                        let
                            valid = Valid { patternSort = objectS1 }
                            top' = TopPattern Top { topSort = objectS1 }
                        in
                            asKorePattern (valid :< top')
                    , sentenceAliasResultSort = objectS1
                    }
                )
            )
            (resolveAlias testIndexedModule (testId "b" :: Id Object))
        )
    , testCase "meta alias"
        (assertEqual ""
            (Right (def :: Attribute.Null, SentenceAlias
                { sentenceAliasAttributes = Attributes []
                , sentenceAliasAlias = sentenceAliasAlias metaB
                , sentenceAliasSorts = []
                , sentenceAliasLeftPattern =
                    Application
                        { applicationSymbolOrAlias =
                            SymbolOrAlias
                                { symbolOrAliasConstructor =
                                    aliasConstructor
                                        (sentenceAliasAlias metaB)
                                , symbolOrAliasParams =
                                    (<$>)
                                        SortVariableSort
                                        (aliasParams
                                            $ sentenceAliasAlias metaB
                                        )
                                }
                        , applicationChildren = []
                        }
                , sentenceAliasRightPattern =
                    let
                        valid = Valid { patternSort = charListMetaSort }
                        top' = TopPattern Top { topSort = charListMetaSort }
                    in
                        asKorePattern (valid :< top')
                , sentenceAliasResultSort = charListMetaSort
                }
            ))
            (resolveAlias testIndexedModule (testId "#b" :: Id Meta))
        )
    , testCase "symbol error"
        (assertEqual ""
            (Left Error
                { errorContext = ["(<test data>)"]
                , errorError = "Symbol '#b' not defined."}
            )
            (resolveSymbol testIndexedModule (testId "#b" :: Id Meta))
        )
    , testCase "alias error"
        (assertEqual ""
            (Left Error
                { errorContext = ["(<test data>)"]
                , errorError = "Alias '#a' not defined."}
            )
            (resolveAlias testIndexedModule (testId "#a" :: Id Meta))
        )
    , testCase "sort error"
        (assertEqual ""
            (Left Error
                { errorContext = ["(<test data>)"]
                , errorError = "Sort '#a' not declared."}
            )
            (resolveSort testIndexedModule (testId "#a" :: Id Meta))
        )
    , testCase "symbol getHeadApplicationSorts"
        (assertEqual ""
            ApplicationSorts
                { applicationSortsOperands = []
                , applicationSortsResult = objectS1
                }
            (getHeadApplicationSorts
                testIndexedModule
                (getSentenceSymbolOrAliasHead objectA [])
            )
        )
    , testCase "alias getHeadApplicationSorts"
        (assertEqual ""
            ApplicationSorts
                { applicationSortsOperands = []
                , applicationSortsResult = objectS1
                }
            (getHeadApplicationSorts
                testIndexedModule
                (getSentenceSymbolOrAliasHead objectB [])
            )
        )
    ]
  where
    SortActualSort charMetaSortActual = charMetaSort
    charMetaId :: Id Meta
    charMetaId = sortActualName charMetaSortActual
