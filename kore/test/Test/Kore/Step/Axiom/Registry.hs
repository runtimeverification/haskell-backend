module Test.Kore.Step.Axiom.Registry (test_functionRegistry) where

import Test.Tasty
    ( TestTree
    )
import Test.Tasty.HUnit
    ( assertEqual
    , assertFailure
    , testCase
    )

import qualified Data.Default as Default
import qualified Data.Map as Map
import Data.Maybe
    ( fromMaybe
    )
import Data.Proxy
    ( Proxy (..)
    )
import Data.Text
    ( Text
    )

import Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Attribute.Axiom as Attribute
import Kore.Attribute.Simplification
    ( simplificationSymbol
    )
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import Kore.Error
    ( printError
    )
import Kore.IndexedModule.IndexedModule
    ( VerifiedModule
    )
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
    ( build
    )
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
    ( AxiomIdentifier (..)
    )
import Kore.Step.Axiom.Registry
import Kore.Step.Rule
    ( extractRewriteAxioms
    )
import qualified Kore.Step.Simplification.Pattern as Pattern
import Kore.Step.Simplification.Simplify
import Kore.Syntax.Definition hiding
    ( Symbol
    )

import Test.Kore
import Test.Kore.ASTVerifier.DefinitionVerifier
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification

updateAttributes :: Attributes -> Sentence patternType -> Sentence patternType
updateAttributes attrs = updateAttrs
  where
    updateAttrs :: Sentence patternType -> Sentence patternType
    updateAttrs (SentenceSymbolSentence ss) =
        SentenceSymbolSentence
            (ss { sentenceSymbolAttributes = attrs })
    updateAttrs _ = error "unsupported non-symbol sentence"

sortVar :: SortVariable
sortVar = SortVariable (testId "R")

sortVar1 :: SortVariable
sortVar1 = SortVariable (testId "R1")

sortVarS :: Sort
sortVarS = SortVariableSort sortVar

sortVar1S :: Sort
sortVar1S = SortVariableSort sortVar1

sortS :: Sort
sortS = SortActualSort (SortActual (testId "S") [])

testSymbol :: Text -> Symbol
testSymbol name =
    Symbol
        { symbolConstructor = testId name
        , symbolParams = []
        , symbolAttributes = Default.def
        , symbolSorts = applicationSorts [] sortS
        }

fHead, gHead, sHead, tHead :: Symbol
fHead = testSymbol "f"
gHead = testSymbol "g"
sHead = testSymbol "s"
tHead = testSymbol "t"

injHead :: Sort -> Sort -> Symbol
injHead s1 s2 =
    (testSymbol "inj")
        { symbolParams = [s1, s2]
        , symbolSorts = applicationSorts [s1] s2
        }

testDef :: Definition ParsedSentence
testDef =
    simpleDefinitionFromSentences
        (ModuleName "test")
        [ simpleSortSentence (SortName "S")
        , simpleSymbolSentence (SymbolName "s") (SortName "S")
        , simpleSymbolSentence (SymbolName "t") (SortName "S")
        , symbolSentenceWithParametersAndArguments
            (SymbolName "inj")
            [sortVar, sortVar1]
            sortVar1S
            [sortVarS]
        , updateAttributes
            (Attributes
                [ Attribute.functionAttribute
                , Attribute.constructorAttribute
                ]
            )
            (simpleSymbolSentence (SymbolName "f") (SortName "S"))
        , updateAttributes
            (Attributes
                [ Attribute.functionAttribute
                , Attribute.constructorAttribute]
            )
            (simpleSymbolSentence (SymbolName "g") (SortName "S"))
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalize $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals
                            sortVarS
                            (mkApplySymbol (injHead sortS sortS)
                                [mkApplySymbol tHead []]
                            )
                            (mkApplySymbol sHead [])
                        )
                        (mkTop sortVarS)
                    )
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalize $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals
                            sortVarS
                            (mkApplySymbol gHead [])
                            (mkApplySymbol sHead [])
                        )
                        (mkTop sortVarS)
                    )
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalize $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals sortVarS
                            (mkTop sortS)
                            (mkApplySymbol fHead [])
                        )
                        (mkTop sortVarS)
                    )
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalize $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals sortVarS
                            (mkApplySymbol fHead [])
                            (mkApplySymbol sHead [])
                        )
                        (mkTop sortVarS)
                    )
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalize $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals sortVarS
                            (mkApplySymbol fHead [])
                            (mkApplySymbol tHead [])
                        )
                        (mkTop sortVarS)
                    )
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes =
                Attributes [ attributePattern_ simplificationSymbol ]
            , sentenceAxiomPattern =
                Builtin.externalize $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals sortVarS
                            (mkApplySymbol fHead [])
                            (mkApplySymbol gHead [])
                        )
                        (mkTop sortVarS)
                    )
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalize $ mkTop sortS
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalize $ mkRewrites
                    (mkAnd mkTop_ (mkApplySymbol fHead []))
                    (mkAnd mkTop_ (mkApplySymbol tHead []))
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar, sortVar1]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalize $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals sortVarS
                            (mkCeil sortVar1S (mkApplySymbol fHead []))
                            mkTop_
                        )
                        (mkTop sortVarS)
                    )
            }
        ]

testIndexedModule :: VerifiedModule Attribute.Symbol Attribute.Axiom
testIndexedModule =
    let
        attributesVerification = defaultAttributesVerification Proxy Proxy
        verifyResult = verifyAndIndexDefinition
            attributesVerification
            Builtin.koreVerifiers
            testDef
    in
        case verifyResult of
            Left err1            -> error (printError err1)
            Right indexedModules ->
                fromMaybe
                    (error "Module not found. Should not be possible.")
                    (Map.lookup (ModuleName "test") indexedModules)

testEvaluators :: BuiltinAndAxiomSimplifierMap
testEvaluators =
    axiomPatternsToEvaluators $ extractEqualityAxioms testIndexedModule

testMetadataTools :: SmtMetadataTools Attribute.Symbol
testMetadataTools = MetadataTools.build testIndexedModule

testEnv :: Env Simplifier
testEnv =
    Mock.env
        { metadataTools = testMetadataTools
        , simplifierAxioms = testEvaluators
        }

test_functionRegistry :: [TestTree]
test_functionRegistry =
    [ testCase "Checking that a simplifier is found for f"
        (let axiomId = AxiomIdentifier.Application (testId "f")
          in
            (case Map.lookup axiomId testEvaluators of
                Just _ -> return ()
                _ -> assertFailure "Should find a simplifier for f"
            )
        )
    , testCase "Checking that a simplifier is found for parametric inj"
        (let axiomId = AxiomIdentifier.Application (testId "inj")
          in
            (case Map.lookup axiomId testEvaluators of
                Just _ -> return ()
                _ -> assertFailure "Should find a simplifier for inj"
            )
        )
    , testCase "Checking that a simplifier is found for ceil(f)"
        (let
            axiomId =
                AxiomIdentifier.Ceil (AxiomIdentifier.Application (testId "f"))
          in
            (case Map.lookup axiomId testEvaluators of
                Just _ -> return ()
                _ -> assertFailure "Should find a simplifier for ceil(f)"
            )
        )
    , testCase "Checking that evaluator map has size 4"
        (assertEqual ""
            4
            (Map.size testEvaluators)
        )
    , testCase "Checking that the indexed module contains a rewrite axiom"
        (assertEqual ""
            (1::Int)
            (length (extractRewriteAxioms testIndexedModule))
        )
    , testCase "Checking that evaluator simplifies correctly" $ do
        let expect = mkApplySymbol sHead []
        simplified <-
            runSimplifier testEnv
            $ Pattern.simplify $ makePattern $ mkApplySymbol gHead []
        let actual =
                Pattern.term $ head
                $ MultiOr.extractPatterns simplified
        assertEqual "" expect actual
    ]
  where
    makePattern :: TermLike Variable -> Pattern Variable
    makePattern = Pattern.fromTermLike
