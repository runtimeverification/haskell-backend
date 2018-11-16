module Test.Kore.IndexedModule.MetadataTools (test_metadataTools) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( assertBool, assertEqual, testCase )

import           Data.Functor.Foldable
                 ( Fix (..) )
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )
import qualified Data.Set as Set
import qualified Data.Text as Text

import           Kore.AST.Builders
import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.AST.PureToKore
import           Kore.AST.Sentence
import           Kore.ASTHelpers
                 ( ApplicationSorts (..) )
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.Attribute.Constructor
import           Kore.Attribute.Functional
import qualified Kore.Attribute.Null as Attribute
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.Implicit.ImplicitSorts
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), extractMetadataTools )
import           Kore.Step.StepperAttributes

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

testIndexedModule :: KoreIndexedModule StepperAttributes
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

metadataTools :: MetaOrObject level => MetadataTools level StepperAttributes
metadataTools = extractMetadataTools testIndexedModule

test_metadataTools :: [TestTree]
test_metadataTools =
    [ testCase "constructor object"
        (assertEqual ""
            (Constructor True)
            (constructor
                $ symAttributes metadataTools
                $ symbolHead objectA
            )
        )
    , testCase "constructor meta"
        (assertEqual ""
            (Constructor False)
            (constructor
                $ symAttributes metadataTools
                $ symbolHead metaA
            )
        )
    , testCase "functional object"
        (assertEqual ""
            (Functional False)
            (functional
                $ symAttributes metadataTools
                $ symbolHead objectA
            )
        )
    , testCase "functional meta"
        (assertEqual ""
            (Functional False)
            (functional
                $ symAttributes metadataTools
                $ symbolHead metaA
            )
        )
    , testCase "getArgumentSorts object"
        (assertEqual ""
            []
            (applicationSortsOperands
                (symbolOrAliasSorts metadataTools (symbolHead objectA)))
        )
    , testCase "getArgumentSorts meta"
        (assertEqual ""
            []
            (applicationSortsOperands
                (symbolOrAliasSorts metadataTools (symbolHead metaA)))
        )
    , testCase "getResultSort object"
        (assertEqual ""
            objectS1
            (applicationSortsResult
                (symbolOrAliasSorts metadataTools (symbolHead objectA)))
        )
    , testCase "getResultSort meta"
        (assertEqual ""
            charListMetaSort
            (applicationSortsResult
                (symbolOrAliasSorts metadataTools (symbolHead metaA)))
        )
    , testGroup "subsort" testSubsorts
    ]
  where
    symbolHead symbol = getSentenceSymbolOrAliasHead symbol []

sortA, sortB, sortC, sortD,sortE, sortF, sortG :: Sort Object
[sortA, sortB, sortC, sortD, sortE, sortF, sortG] =
    [(sortActual . Text.pack) [c] [] | c <- "ABCDEFG"]

sortVarR :: Sort Object
sortVarR = sortVariableSort "R"

testSubsorts :: [TestTree]
testSubsorts =
    [ test "direct subsort" (isSubsortOf meta sortA sortB)
    , test "transitive subsort" (isSubsortOf meta sortA sortC)
    , test "not subsort, known sorts" (not (isSubsortOf meta sortD sortE))
    , test "not subsort, unknown sorts" (not (isSubsortOf meta sortF sortG))
    , testSubsort
        "subsorts reflexivity"
        [sortA]
        (subsorts meta sortA)
    , testSubsort
        "direct subsorts"
        [sortA, sortB]
        (subsorts meta sortB)
    , testSubsort
        "transitive subsorts"
        [sortA, sortB, sortC]
        (subsorts meta sortC)
    ]
  where
    test name cond = testCase name (assertBool "" cond)
    testSubsort name list = testCase name . assertEqual "" (Set.fromList list)
    moduleIndex :: Map.Map ModuleName (KoreIndexedModule Attribute.Null)
    Right moduleIndex = verifyAndIndexDefinition DoNotVerifyAttributes
        Builtin.koreVerifiers
        testSubsortDefinition
    meta :: MetadataTools Object Attribute.Null
    meta = extractMetadataTools $ moduleIndex Map.! testObjectModuleName


testSubsortDefinition :: KoreDefinition
testSubsortDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules = [ testSubsortModule ]
        }

testSubsortModule :: KoreModule
testSubsortModule =
    Module
        { moduleName = testObjectModuleName
        , moduleSentences =
            [ sortDecl sortA
            , sortDecl sortB
            , sortDecl sortC
            , sortDecl sortD
            , sortDecl sortE
            , subsortAxiom sortA sortB
            , subsortAxiom sortB sortC
            ]
        , moduleAttributes = Attributes []
        }
  where
    subsortAxiom :: Sort Object -> Sort Object -> KoreSentence
    subsortAxiom subSort superSort =
        constructUnifiedSentence SentenceAxiomSentence $
          (SentenceAxiom
              { sentenceAxiomParameters = [UnifiedObject (sortVariable "R")]
              , sentenceAxiomPattern =
                  Fix . asUnifiedPattern $ TopPattern (Top sortVarR)
              , sentenceAxiomAttributes = Attributes
                  [subsortAttribute subSort superSort]
              })
    subsortAttribute :: Sort Object -> Sort Object -> KorePattern Variable
    subsortAttribute subSort superSort = Fix . asUnifiedPattern $
        (ApplicationPattern (Application
            (SymbolOrAlias (testId "subsort") [subSort,superSort])
            []))
    sortDecl :: Sort Object -> KoreSentence
    sortDecl (SortActualSort (SortActual name [])) =
        constructUnifiedSentence SentenceSortSentence $
          (SentenceSort
              { sentenceSortName = name
              , sentenceSortParameters = []
              , sentenceSortAttributes = Attributes []
              })
    sortDecl _ = error "Cannot make sort declaration from this Sort expression"

{- subsorting axioms look like this:
 axiom{R} \exists{R} (Val:SortKResult{},
    \equals{SortKResult{}, R}
       (Val:SortKResult{},
        inj{SortBool{}, SortKResult{}} (From:SortBool{}))) [subsort{SortBool{}, SortKResult{}}()] // subsort
 -}
