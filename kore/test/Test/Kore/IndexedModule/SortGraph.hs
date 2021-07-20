module Test.Kore.IndexedModule.SortGraph (
    test_isSubsortOf,
    test_subsortsOf,
    test_fromIndexedModule,
) where

import qualified Data.Map.Strict as Map
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import Kore.Attribute.Subsort (
    subsortAttribute,
 )
import qualified Kore.Builtin as Builtin
import Kore.Error (
    assertRight,
 )
import Kore.IndexedModule.SortGraph
import Kore.Internal.TermLike (
    mkTop,
 )
import Kore.Sort
import Kore.Syntax.Definition
import Kore.Validate.DefinitionVerifier (
    verifyAndIndexDefinition,
 )
import Prelude.Kore
import Test.Kore
import Test.Kore.Builtin.External
import Test.Tasty
import Test.Tasty.HUnit.Ext

sortA, sortB, sortC, sortD :: Sort
sortA = sortActual "A" []
sortB = sortActual "B" []
sortC = sortActual "C" []
sortD = sortActual "D" []

sortVarR :: Sort
sortVarR = sortVariableSort "R"

sortGraph :: SortGraph
sortGraph =
    fromSubsorts
        [ Subsort{supersort = sortB, subsort = sortA}
        , Subsort{supersort = sortC, subsort = sortB}
        ]

isSubsortOf' :: Sort -> Sort -> Bool
isSubsortOf' = isSubsortOf sortGraph

subsortsOf' :: Sort -> Set Sort
subsortsOf' = subsortsOf sortGraph

test_isSubsortOf :: [TestTree]
test_isSubsortOf =
    [ test "direct subsort" (isSubsortOf' sortA sortB)
    , test "transitive subsort" (isSubsortOf' sortA sortC)
    , test "not subsort, known sorts" (not (isSubsortOf' sortC sortD))
    , test "not subsort, sort variable" (not (isSubsortOf' sortA sortVarR))
    ]
  where
    test name cond = testCase name (assertBool "" cond)

test_subsortsOf :: [TestTree]
test_subsortsOf =
    [ test "direct subsorts" [sortA, sortB] (subsortsOf' sortB)
    , test "transitive subsorts" [sortA, sortB, sortC] (subsortsOf' sortC)
    ]
  where
    test name list = testCase name . assertEqual "" (Set.fromList list)

test_fromIndexedModule :: TestTree
test_fromIndexedModule =
    testCase "fromIndexedModule = fromSubsorts" $
        assertEqual "" sortGraph (fromIndexedModule verifiedModule)
  where
    verifiedModules =
        assertRight $ verifyAndIndexDefinition Builtin.koreVerifiers definition

    verifiedModule =
        fromMaybe
            (error $ "Missing module: " ++ show testModuleName)
            (Map.lookup testModuleName verifiedModules)

    definition =
        Definition
            { definitionAttributes = Attributes []
            , definitionModules = [subsortsModule]
            }

    subsortsModule =
        Module
            { moduleName = testModuleName
            , moduleSentences =
                [ sortDecl sortA
                , sortDecl sortB
                , sortDecl sortC
                , sortDecl sortD
                , subsortAxiom sortA sortB
                , subsortAxiom sortB sortC
                ]
            , moduleAttributes = Attributes []
            }

    testModuleName = "SUBSORTS"

    subsortAxiom :: Sort -> Sort -> ParsedSentence
    subsortAxiom subSort superSort =
        SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVariable "R"]
                , sentenceAxiomPattern = externalize (mkTop sortVarR)
                , sentenceAxiomAttributes =
                    Attributes
                        [subsortAttribute subSort superSort]
                }

    sortDecl :: Sort -> ParsedSentence
    sortDecl (SortActualSort (SortActual name [])) =
        SentenceSortSentence
            SentenceSort
                { sentenceSortName = name
                , sentenceSortParameters = []
                , sentenceSortAttributes = Attributes []
                }
    sortDecl _ = error "Cannot make sort declaration from this Sort expression"
