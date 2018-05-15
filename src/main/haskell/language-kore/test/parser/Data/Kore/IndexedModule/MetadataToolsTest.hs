module Data.Kore.IndexedModule.MetadataToolsTest where

import           Data.Kore.AST.Builders
import           Data.Kore.AST.Common
import           Data.Kore.AST.Kore
import           Data.Kore.AST.MetaOrObject
import           Data.Kore.AST.PureML
import           Data.Kore.AST.PureToKore
import           Data.Kore.ASTVerifier.DefinitionVerifier
import           Data.Kore.ASTVerifier.DefinitionVerifierTestHelpers
import           Data.Kore.Error
import           Data.Kore.IndexedModule.IndexedModule
import           Data.Kore.IndexedModule.MetadataTools


import           Test.Tasty                                          (TestTree,
                                                                      testGroup)
import           Test.Tasty.HUnit                                    (assertEqual,
                                                                      testCase)
import           Test.Tasty.QuickCheck                               (forAll, testProperty)

import qualified Data.Map                                            as Map
import           Data.Maybe                                          (fromMaybe)

objectS1 :: Sort Object
objectS1 = simpleSort (SortName "s1")

metaS1 :: Sort Meta
metaS1 = simpleSort (SortName "#s1")

objectA :: PureSentenceSymbol Object
objectA = symbol_ "a" AstLocationTest [] objectS1

metaA :: PureSentenceSymbol Meta
metaA = symbol_ "a" AstLocationTest [] metaS1

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
        , moduleSentences = [ asSentence objectA ]
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
        [ testCase "constructor 1"
            (assertEqual ""
                True
                (isConstructor metadataTools (symbolHead objectA))
            )
        , testCase "constructor 2"
            (assertEqual ""
                True
                (isConstructor metadataTools (symbolHead metaA))
            )
        ]
  where
    symbolHead symbol = getSentenceSymbolOrAliasHead symbol []
