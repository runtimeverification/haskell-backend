module Test.Kore.IndexedModule.MetadataTools (test_metadataTools) where

import Test.Tasty
    ( TestTree
    , testGroup
    )
import Test.Tasty.HUnit
    ( assertBool
    , assertEqual
    , testCase
    )

import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Text as Text

import Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Subsort
    ( subsortAttribute
    )
import Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import Kore.IndexedModule.IndexedModule
import Kore.IndexedModule.MetadataTools
    ( MetadataTools (..)
    , extractMetadataTools
    )
import Kore.Internal.TermLike
import Kore.Syntax.Definition

import Test.Kore

testObjectModuleName :: ModuleName
testObjectModuleName = ModuleName "TEST-OBJECT-MODULE"

test_metadataTools :: [TestTree]
test_metadataTools =
    [ testGroup "subsort" testSubsorts ]

sortA, sortB, sortC, sortD,sortE, sortF, sortG :: Sort
[sortA, sortB, sortC, sortD, sortE, sortF, sortG] =
    [(sortActual . Text.pack) [c] [] | c <- "ABCDEFG"]

sortVarR :: Sort
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
    moduleIndex ::
        Map.Map ModuleName (VerifiedModule Attribute.Symbol Attribute.Axiom)
    Right moduleIndex =
        verifyAndIndexDefinition
            DoNotVerifyAttributes
            Builtin.koreVerifiers
            testSubsortDefinition
    meta :: MetadataTools () () Attribute.Symbol
    meta =
        extractMetadataTools
            (moduleIndex Map.! testObjectModuleName)
            (const Map.empty)
            (const $ const ())


testSubsortDefinition :: ParsedDefinition
testSubsortDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules = [ testSubsortModule ]
        }

testSubsortModule :: ParsedModule
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
    subsortAxiom :: Sort -> Sort -> ParsedSentence
    subsortAxiom subSort superSort =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVariable "R"]
            , sentenceAxiomPattern =
                Builtin.externalize (mkTop sortVarR)
            , sentenceAxiomAttributes = Attributes
                [subsortAttribute subSort superSort]
            }

    sortDecl :: Sort -> ParsedSentence
    sortDecl (SortActualSort (SortActual name [])) =
        SentenceSortSentence
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
