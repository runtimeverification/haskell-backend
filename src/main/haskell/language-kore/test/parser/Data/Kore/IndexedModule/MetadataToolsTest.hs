module Data.Kore.IndexedModule.MetadataToolsTest where

import           Test.Tasty                                          (TestTree,
                                                                      testGroup)
import           Test.Tasty.HUnit                                    (assertEqual,
                                                                      testCase)
import           Data.Fix
import qualified Data.Map                                            as Map
import           Data.Maybe                                          (fromMaybe)

import           Data.Kore.AST.Builders
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.AST.PureToKore
import           Data.Kore.ASTVerifier.DefinitionVerifier
import           Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers
import           Data.Kore.Error
import           Data.Kore.Implicit.ImplicitSorts
import           Data.Kore.Implicit.Attributes
import           Data.Kore.IndexedModule.IndexedModule
import           Data.Kore.IndexedModule.MetadataTools
import           Data.Kore.KoreHelpers


objectS1 :: Sort Object
objectS1 = simpleSort (SortName "s1")

objectA :: PureSentenceSymbol Object
objectA = SentenceSymbol
    { sentenceSymbolSymbol = 
        Symbol
          { symbolConstructor = (Id "b" AstLocationNone)
          , symbolParams = []
          }
    , sentenceSymbolSorts = []
    , sentenceSymbolResultSort = objectS1
    , sentenceSymbolAttributes = Attributes [ constructorAttribute ]
    }

metaA :: PureSentenceSymbol Meta
metaA = symbol_ "#a" AstLocationTest [] charListMetaSort

testObjectModuleName :: ModuleName
testObjectModuleName = ModuleName "TEST-OBJECT-MODULE"

testMetaModuleName :: ModuleName
testMetaModuleName = ModuleName "TEST-META-MODULE"

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
            ]
        , moduleAttributes = Attributes []
        }

testMetaModule :: PureModule Meta
testMetaModule =
    Module
        { moduleName = testMetaModuleName
        , moduleSentences = [ asSentence metaA ]
        , moduleAttributes = Attributes []
        }

mainModule :: KoreModule
mainModule =
    Module
        { moduleName = testMainModuleName
        , moduleSentences =
            [ importSentence testObjectModuleName
            , importSentence testMetaModuleName
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

metadataTools :: MetaOrObject level => MetadataTools level
metadataTools = extractMetadataTools testIndexedModule

metadataToolsTests :: TestTree
metadataToolsTests =
    testGroup
        "MetadataTools unit tests"
        [ testCase "constructor object"
            (assertEqual ""
                True
                (isConstructor metadataTools (symbolHead objectA))
            )
        , testCase "constructor meta"
            (assertEqual ""
                False
                (isConstructor metadataTools (symbolHead metaA))
            )
        , testCase "functional object"
            (assertEqual ""
                False
                (isFunctional metadataTools (symbolHead metaA))
            )
        , testCase "functional meta"
            (assertEqual ""
                False
                (isFunctional metadataTools (symbolHead metaA))
            )
        , testCase "getArgumentSorts object"
            (assertEqual ""
                []
                (getArgumentSorts metadataTools (symbolHead objectA))
            )
        , testCase "getArgumentSorts meta"
            (assertEqual ""
                []
                (getArgumentSorts metadataTools (symbolHead metaA))
            )
        , testCase "getResultSort object"
            (assertEqual ""
                objectS1
                (getResultSort metadataTools (symbolHead objectA))
            )
        , testCase "getResultSort meta"
            (assertEqual ""
                charListMetaSort
                (getResultSort metadataTools (symbolHead metaA))
            )
        ]
  where
    symbolHead symbol = getSentenceSymbolOrAliasHead symbol []
