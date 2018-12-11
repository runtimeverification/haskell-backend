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
import           Kore.AST.Builders
import           Kore.AST.Pure
import           Kore.AST.PureToKore
import           Kore.AST.Sentence
import           Kore.ASTHelpers
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Builtin as Builtin
import qualified Kore.Domain.Builtin as Domain
import           Kore.Error
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.Resolvers
import           Kore.Step.Pattern

import Test.Kore
import Test.Kore.ASTVerifier.DefinitionVerifier

objectS1 :: Sort Object
objectS1 = simpleSort (SortName "s1")

objectA :: PureSentenceSymbol Object Domain.Builtin
objectA = symbol_ "a" AstLocationTest [] objectS1

objectB :: PureSentenceAlias Object Domain.Builtin
objectB = alias_ "b" AstLocationTest objectS1 [] (Top_ objectS1)

metaA :: PureSentenceSymbol Meta Domain.Builtin
metaA = symbol_ "#a" AstLocationTest [] charListMetaSort

metaB :: PureSentenceAlias Meta Domain.Builtin
metaB = alias_ "#b" AstLocationTest charListMetaSort [] (Top_ charListMetaSort)

testObjectModuleName :: ModuleName
testObjectModuleName = ModuleName "TEST-OBJECT-MODULE"

testMetaModuleName :: ModuleName
testMetaModuleName = ModuleName "TEST-META-MODULE"

testSubMainModuleName :: ModuleName
testSubMainModuleName = ModuleName "TEST-SUB-MAIN-MODULE"

testMainModuleName :: ModuleName
testMainModuleName = ModuleName "TEST-MAIN-MODULE"

testObjectModule :: PureModule Object Domain.Builtin
testObjectModule =
    Module
        { moduleName = testObjectModuleName
        , moduleSentences =
            [ SentenceSortSentence
                SentenceSort
                    { sentenceSortName = testId "s1"
                    , sentenceSortParameters = []
                    , sentenceSortAttributes =
                        Attributes
                            [patternPureToKore
                                (App_ (groundHead "strict" AstLocationTest)
                                    []
                                ::CommonStepPattern Object)
                            ]
                    }
            , asSentence objectA
            , asSentence objectB
            ]
        , moduleAttributes =
            Attributes
                [patternPureToKore
                    (App_ (groundHead "strict" AstLocationTest)
                        []
                    ::CommonStepPattern Object)
                ]
        }

testMetaModule :: PureModule Meta Domain.Builtin
testMetaModule =
    Module
        { moduleName = testMetaModuleName
        , moduleSentences =
            [ asSentence metaA
            , asSentence metaB
            ]
        , moduleAttributes = Attributes []
        }

subMainModule :: KoreModule
subMainModule =
    Module
        { moduleName = testSubMainModuleName
        , moduleSentences =
            [ importSentence testMetaModuleName
            , importSentence testObjectModuleName
            ]
        , moduleAttributes =
            Attributes
                [patternPureToKore
                    (App_ (groundHead "strict" AstLocationTest)
                        []
                    ::CommonStepPattern Object)
                ]
        }

mainModule :: KoreModule
mainModule =
    Module
        { moduleName = testMainModuleName
        , moduleSentences =
            [ importSentence testMetaModuleName
            , importSentence testSubMainModuleName
            ]
        , moduleAttributes = Attributes []
        }


testDefinition :: KoreDefinition
testDefinition =
    Definition
        { definitionAttributes =
            Attributes
            [patternPureToKore
                (App_ (groundHead "strict" AstLocationTest)
                    []
                ::CommonStepPattern Object)
            ]
        , definitionModules =
            [ modulePureToKore testObjectModule
            , modulePureToKore testMetaModule
            , subMainModule
            , mainModule
            ]
        }

testIndexedModule :: VerifiedModule Attribute.Null
testIndexedModule =
    case
        verifyAndIndexDefinition
            DoNotVerifyAttributes
            Builtin.koreVerifiers
            testDefinition
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
                , sentenceSortAttributes =
                    Attributes
                        [patternPureToKore
                            (App_ (groundHead "strict" AstLocationTest)
                                []
                            ::CommonStepPattern Object)
                        ]
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
                        patternPureToKore
                            (Valid { patternSort = objectS1 } <$ Top_ objectS1)
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
                    patternPureToKore
                        (Valid { patternSort = charListMetaSort }
                            <$ Top_ charListMetaSort)
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
