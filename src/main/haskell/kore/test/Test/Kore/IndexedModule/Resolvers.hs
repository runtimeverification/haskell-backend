module Test.Kore.IndexedModule.Resolvers (test_resolvers) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import           Data.Default
import           Data.Functor.Foldable
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )

import Kore.AST.Builders
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.PureML
import Kore.AST.PureToKore
import Kore.AST.Sentence
import Kore.ASTHelpers
import Kore.ASTUtils.SmartPatterns
import Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.Implicit.Attributes
import Kore.Implicit.ImplicitSorts
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.Resolvers

import Test.Kore
import Test.Kore.ASTVerifier.DefinitionVerifier

objectS1 :: Sort Object
objectS1 = simpleSort (SortName "s1")

topPatMeta :: Pattern Meta variable (Fix (pat variable))
topPatMeta = TopPattern $ Top { topSort = patternMetaSort }

topPatObj :: Pattern Object variable (Fix (pat variable))
topPatObj  = TopPattern $ Top { topSort = objectS1 }

objectA :: PureSentenceSymbol Object
objectA = symbol_ "a" AstLocationTest [] objectS1

objectB :: PureSentenceAlias Object
objectB = alias_ "b" AstLocationTest [] objectS1 topPatObj topPatObj

metaA :: PureSentenceSymbol Meta
metaA = symbol_ "#a" AstLocationTest [] charListMetaSort

metaB :: PureSentenceAlias Meta
metaB = alias_ "#b" AstLocationTest [] charListMetaSort topPatMeta topPatMeta

testObjectModuleName :: ModuleName
testObjectModuleName = ModuleName "TEST-OBJECT-MODULE"

testMetaModuleName :: ModuleName
testMetaModuleName = ModuleName "TEST-META-MODULE"

testSubMainModuleName :: ModuleName
testSubMainModuleName = ModuleName "TEST-SUB-MAIN-MODULE"

testMainModuleName :: ModuleName
testMainModuleName = ModuleName "TEST-MAIN-MODULE"

testObjectModule :: PureModule Object
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
                                ::CommonPurePattern Object)
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
                    ::CommonPurePattern Object)
                ]
        }

testMetaModule :: PureModule Meta
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
                    ::CommonPurePattern Object)
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
                ::CommonPurePattern Object)
            ]
        , definitionModules =
            [ modulePureToKore testObjectModule
            , modulePureToKore testMetaModule
            , subMainModule
            , mainModule
            ]
        }

testIndexedModule :: KoreIndexedModule ImplicitAttributes
testIndexedModule =
    case
        verifyAndIndexDefinition
            DoNotVerifyAttributes
            Builtin.koreBuiltins
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
            (Right (def :: ImplicitAttributes, SentenceSort
                { sentenceSortName = testId "s1"
                , sentenceSortParameters = []
                , sentenceSortAttributes =
                    Attributes
                        [patternPureToKore
                            (App_ (groundHead "strict" AstLocationTest)
                                []
                            ::CommonPurePattern Object)
                        ]
                })
            )
            (resolveSort testIndexedModule (testId "s1" :: Id Object))
        )
    , testCase "meta sort"
        (assertEqual ""
            (Right (def :: ImplicitAttributes, SentenceSort
                { sentenceSortName = charMetaId
                , sentenceSortParameters = []
                , sentenceSortAttributes = Attributes []
                }
            ))
            (resolveSort testIndexedModule charMetaId)
        )
    , testCase "object symbol"
        (assertEqual ""
            (Right (def :: ImplicitAttributes, SentenceSymbol
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
            (Right (def :: ImplicitAttributes, SentenceSymbol
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
            (Right (def :: ImplicitAttributes, SentenceAlias
                { sentenceAliasAttributes = Attributes []
                , sentenceAliasAlias = sentenceAliasAlias objectB
                , sentenceAliasSorts = []
                , sentenceAliasLeftPattern = topPatObj
                , sentenceAliasRightPattern = topPatObj
                , sentenceAliasResultSort = objectS1
                }
            ))
            (resolveAlias testIndexedModule (testId "b" :: Id Object))
        )
    , testCase "meta alias"
        (assertEqual ""
            (Right (def :: ImplicitAttributes, SentenceAlias
                { sentenceAliasAttributes = Attributes []
                , sentenceAliasAlias = sentenceAliasAlias metaB
                , sentenceAliasSorts = []
                , sentenceAliasLeftPattern = topPatMeta
                , sentenceAliasRightPattern = topPatMeta
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
