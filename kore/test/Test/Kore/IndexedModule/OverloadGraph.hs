module Test.Kore.IndexedModule.OverloadGraph (
    test_isOverloaded,
    test_isOverloading,
    test_commonOverloads,
    test_fromIndexedModule,
) where

import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Kore.Attribute.Overload (
    overloadAttribute,
 )
import qualified Kore.Builtin as Builtin
import Kore.Error (
    assertRight,
 )
import Kore.IndexedModule.OverloadGraph
import Kore.Internal.Symbol
import Kore.Internal.TermLike (
    Sort,
    mkTop,
 )
import Kore.Syntax.Definition (
    Attributes (..),
    Definition (..),
    Module (..),
    ParsedSentence,
    Sentence (..),
    SentenceAxiom (..),
 )
import Kore.Validate.DefinitionVerifier (
    verifyAndIndexDefinition,
 )
import Prelude.Kore
import Test.Kore
import qualified Test.Kore.Builtin.Definition as Definition
import Test.Kore.Builtin.External
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

symbolA, symbolB, symbolC, symbolD, symbolE :: Symbol
symbolA = Mock.symbol "A" [] Mock.testSort
symbolB = Mock.symbol "B" [] Mock.testSort
symbolC = Mock.symbol "C" [] Mock.testSort
symbolD = Mock.symbol "D" [] Mock.testSort
symbolE = Mock.symbol "E" [] Mock.testSort

overloadGraph :: OverloadGraph
overloadGraph =
    fromOverloads
        [ (symbolD, symbolA)
        , (symbolD, symbolB)
        , (symbolD, symbolC)
        , (symbolB, symbolA)
        , (symbolC, symbolA)
        ]

isOverloaded' :: Symbol -> Bool
isOverloaded' = isOverloaded overloadGraph

isOverloading' :: Symbol -> Symbol -> Bool
isOverloading' = isOverloading overloadGraph

commonOverloads' :: Symbol -> Symbol -> [Symbol]
commonOverloads' = commonOverloads overloadGraph

test_isOverloaded :: [TestTree]
test_isOverloaded =
    [ test "overloaded, lowest" (isOverloaded' symbolA)
    , test "overloaded, highest" (isOverloaded' symbolD)
    , test "not overloaded" (not (isOverloaded' symbolE))
    ]
  where
    test name cond = testCase name (assertBool "" cond)

test_isOverloading :: [TestTree]
test_isOverloading =
    [ test "overloading" (isOverloading' symbolD symbolB)
    , test
        "not overloading, known symbols, comparable"
        (not (isOverloading' symbolA symbolB))
    , test
        "not overloading, known symbols, not comparable"
        (not (isOverloading' symbolB symbolC))
    , test
        "not overloading, symbol not overloaded"
        (not (isOverloading' symbolD symbolE))
    ]
  where
    test name cond = testCase name (assertBool "" cond)

test_commonOverloads :: [TestTree]
test_commonOverloads =
    [ test
        "same symbol"
        [symbolB, symbolC, symbolD]
        (commonOverloads' symbolA symbolA)
    , test
        "unifiable symbols"
        [symbolD]
        (commonOverloads' symbolB symbolC)
    , test
        "non-unifiable symbols"
        []
        (commonOverloads' symbolA symbolE)
    ]
  where
    test name expected actual =
        testCase
            name
            (assertEqual "" (Set.fromList expected) (Set.fromList actual))

test_fromIndexedModule :: TestTree
test_fromIndexedModule =
    testCase "fromIndexedModule = fromSubsorts" $
        assertEqual
            ""
            overloadGraph
            (fromIndexedModule verifiedModule)
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
            , definitionModules = [overloadsModule]
            }

    overloadsModule =
        Module
            { moduleName = testModuleName
            , moduleSentences =
                [ Definition.sortDecl Mock.testSort
                , Definition.symbolDecl symbolA
                , Definition.symbolDecl symbolB
                , Definition.symbolDecl symbolC
                , Definition.symbolDecl symbolD
                , Definition.symbolDecl symbolE
                , overloadAxiom symbolD symbolC
                , overloadAxiom symbolD symbolB
                , overloadAxiom symbolD symbolA
                , overloadAxiom symbolC symbolA
                , overloadAxiom symbolB symbolA
                ]
            , moduleAttributes = Attributes []
            }

    testModuleName = "OVERLOADS"

    overloadAxiom :: Symbol -> Symbol -> ParsedSentence
    overloadAxiom
        (toSymbolOrAlias -> overloading)
        (toSymbolOrAlias -> overloaded) =
            SentenceAxiomSentence
                SentenceAxiom
                    { sentenceAxiomParameters = [sortVariable "R"]
                    , sentenceAxiomPattern = externalize (mkTop sortVarR)
                    , sentenceAxiomAttributes =
                        Attributes
                            [overloadAttribute overloading overloaded]
                    }

    sortVarR :: Sort
    sortVarR = sortVariableSort "R"
