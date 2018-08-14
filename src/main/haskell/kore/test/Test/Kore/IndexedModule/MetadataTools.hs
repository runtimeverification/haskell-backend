module Test.Kore.IndexedModule.MetadataTools (test_metadataTools) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )

import Kore.AST.Builders
import Kore.ASTHelpers
import Kore.AST.Common
import Kore.AST.MetaOrObject
import Kore.AST.PureML
import Kore.AST.PureToKore
import Kore.AST.Sentence
import Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Builtin as Builtin
import Kore.Error
import Kore.Implicit.Attributes
import Kore.Implicit.ImplicitSorts
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.MetadataTools
import Kore.Step.StepperAttributes

import Test.Kore
import Test.Kore.ASTVerifier.DefinitionVerifier

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
    , sentenceSymbolAttributes = Attributes [ keyOnlyAttribute "constructor" ]
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

testIndexedModule :: KoreIndexedModule StepperAttributes
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

metadataTools :: MetaOrObject level => MetadataTools level StepperAttributes
metadataTools = extractMetadataTools testIndexedModule

test_metadataTools :: [TestTree]
test_metadataTools =
    [ testCase "constructor object"
        (assertEqual ""
            True
            (isConstructor (attributes metadataTools (symbolHead objectA)))
        )
    , testCase "constructor meta"
        (assertEqual ""
            False
            (isConstructor (attributes metadataTools (symbolHead metaA)))
        )
    , testCase "functional object"
        (assertEqual ""
            False
            (isFunctional (attributes metadataTools (symbolHead metaA)))
        )
    , testCase "functional meta"
        (assertEqual ""
            False
            (isFunctional (attributes metadataTools (symbolHead metaA)))
        )
    , testCase "getArgumentSorts object"
        (assertEqual ""
            []
            (applicationSortsOperands
                (sortTools metadataTools (symbolHead objectA)))
        )
    , testCase "getArgumentSorts meta"
        (assertEqual ""
            []
            (applicationSortsOperands
                (sortTools metadataTools (symbolHead metaA)))
        )
    , testCase "getResultSort object"
        (assertEqual ""
            objectS1
            (applicationSortsResult
                (sortTools metadataTools (symbolHead objectA)))
        )
    , testCase "getResultSort meta"
        (assertEqual ""
            charListMetaSort
            (applicationSortsResult
                (sortTools metadataTools (symbolHead metaA)))
        )
    ]
  where
    symbolHead symbol = getSentenceSymbolOrAliasHead symbol []
