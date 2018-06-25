module Data.Kore.IndexedModule.ResolversTest where

import           Test.Tasty                                          (TestTree,
                                                                      testGroup)
import           Test.Tasty.HUnit                                    (assertEqual,
                                                                      testCase)

import qualified Data.Map                                            as Map
import           Data.Maybe                                          (fromMaybe)
import           Data.Fix

import           Data.Kore.AST.Builders
import           Data.Kore.AST.Common
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.AST.PureToKore
import           Data.Kore.AST.Sentence
import           Data.Kore.ASTHelpers
import           Data.Kore.ASTVerifier.DefinitionVerifier
import           Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers
import           Data.Kore.Error
import           Data.Kore.Implicit.ImplicitSorts
import           Data.Kore.IndexedModule.IndexedModule
import           Data.Kore.IndexedModule.Resolvers
import           Data.Kore.KoreHelpers

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
                    , sentenceSortAttributes = Attributes []
                    }
            , asSentence objectA
            , asSentence objectB
            ]
        , moduleAttributes = Attributes []
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
        , moduleAttributes = Attributes []
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
        { definitionAttributes = Attributes []
        , definitionModules =
            [ modulePureToKore testObjectModule
            , modulePureToKore testMetaModule
            , subMainModule
            , mainModule
            ]
        }

testIndexedModule :: KoreIndexedModule
testIndexedModule =
    case verifyAndIndexDefinition DoNotVerifyAttributes testDefinition of
        Right modulesMap ->
            fromMaybe
                (error "This should not have happened")
                (Map.lookup testMainModuleName modulesMap)
        Left err -> error (printError err)

resolversTests :: TestTree
resolversTests =
    testGroup
        "IndexedModule Resolvers unit tests"
        [ testCase "object sort"
            (assertEqual ""
                (Right SentenceSort
                    { sentenceSortName = testId "s1"
                    , sentenceSortParameters = []
                    , sentenceSortAttributes = Attributes []
                    }
                )
                (resolveSort testIndexedModule (testId "s1" :: Id Object))
            )
        , testCase "meta sort"
            (assertEqual ""
                (Right SentenceSort
                    { sentenceSortName = charMetaId
                    , sentenceSortParameters = []
                    , sentenceSortAttributes = Attributes []
                    }
                )
                (resolveSort testIndexedModule charMetaId)
            )
        , testCase "object symbol"
            (assertEqual ""
                (Right SentenceSymbol
                    { sentenceSymbolAttributes = Attributes []
                    , sentenceSymbolSymbol = sentenceSymbolSymbol objectA
                    , sentenceSymbolSorts = []
                    , sentenceSymbolResultSort = objectS1
                    }
                )
                (resolveSymbol testIndexedModule (testId "a" :: Id Object))
            )
        , testCase "meta symbol"
            (assertEqual ""
                (Right SentenceSymbol
                    { sentenceSymbolAttributes = Attributes []
                    , sentenceSymbolSymbol = sentenceSymbolSymbol metaA
                    , sentenceSymbolSorts = []
                    , sentenceSymbolResultSort = charListMetaSort
                    }
                )
                (resolveSymbol testIndexedModule (testId "#a" :: Id Meta))
            )
        , testCase "object alias"
            (assertEqual ""
                (Right SentenceAlias
                    { sentenceAliasAttributes = Attributes []
                    , sentenceAliasAlias = sentenceAliasAlias objectB
                    , sentenceAliasSorts = []
                    , sentenceAliasLeftPattern = topPatObj
                    , sentenceAliasRightPattern = topPatObj
                    , sentenceAliasResultSort = objectS1
                    }
                )
                (resolveAlias testIndexedModule (testId "b" :: Id Object))
            )
        , testCase "meta alias"
            (assertEqual ""
                (Right SentenceAlias
                    { sentenceAliasAttributes = Attributes []
                    , sentenceAliasAlias = sentenceAliasAlias metaB
                    , sentenceAliasSorts = []
                    , sentenceAliasLeftPattern = topPatMeta
                    , sentenceAliasRightPattern = topPatMeta
                    , sentenceAliasResultSort = charListMetaSort
                    }
                )
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
