module Test.Kore.Rewrite.Axiom.Registry (
    test_functionRegistry,
) where

import qualified Data.Default as Default
import qualified Kore.Validate as Validated
import qualified Data.Map.Strict as Map
import Data.Text (
    Text,
 )
import qualified Kore.Attribute.Owise as Attribute
import Kore.Attribute.Priority (
    defaultPriority,
    owisePriority,
 )
import qualified Kore.Attribute.Priority as Attribute
import Kore.Attribute.Simplification (
    simplificationAttribute,
 )
import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Builtin as Builtin
import qualified Kore.Equation as Equation
import Kore.Equation.Registry
import Kore.Error (
    printError,
 )
import Kore.IndexedModule.IndexedModule (
    ValidatedModule,
 )
import Kore.IndexedModule.MetadataTools (
    SmtMetadataTools,
 )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools (
    build,
 )
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike
import qualified Kore.Rewrite.Axiom.Identifier as AxiomIdentifier (
    AxiomIdentifier (..),
 )
import Kore.Rewrite.Axiom.Registry
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
   mkConfigVariable,
 )
import Kore.Rewrite.Rule (
    extractRewriteAxioms,
 )
import qualified Kore.Simplify.Pattern as Pattern
import Kore.Simplify.Simplify
import Kore.Syntax.Definition hiding (
    Symbol,
 )
import Kore.Validate.DefinitionVerifier
import Prelude.Kore
import Test.Kore
import Test.Kore.Builtin.External
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.Kore.Validate.DefinitionVerifier
import Test.Tasty (
    TestTree,
 )
import Test.Tasty.HUnit (
    assertEqual,
    assertFailure,
    testCase,
 )

type PartitionedEquationsMap =
    Map.Map AxiomIdentifier.AxiomIdentifier PartitionedEquations

updateAttributes :: Attributes -> Sentence patternType -> Sentence patternType
updateAttributes attrs = updateAttrs
  where
    updateAttrs :: Sentence patternType -> Sentence patternType
    updateAttrs (SentenceSymbolSentence ss) =
        SentenceSymbolSentence
            (ss{sentenceSymbolAttributes = attrs})
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
        & Symbol.function

fHead, gHead, pHead, qHead, sHead, tHead :: Symbol
fHead = testSymbol "f"
gHead = testSymbol "g"
sHead = testSymbol "s"
tHead = testSymbol "t"
pHead = testSymbol "p"
qHead = testSymbol "q"

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
            & (updateAttributes . Attributes)
                [ Attribute.functionalAttribute
                , Attribute.constructorAttribute
                ]
        , simpleSymbolSentence (SymbolName "t") (SortName "S")
            & (updateAttributes . Attributes)
                [ Attribute.functionalAttribute
                , Attribute.constructorAttribute
                ]
        , symbolSentenceWithParametersAndArguments
            (SymbolName "inj")
            [sortVar, sortVar1]
            sortVar1S
            [sortVarS]
            & updateAttributes (Attributes [Attribute.functionAttribute])
        , updateAttributes
            ( Attributes
                [ Attribute.functionAttribute
                ]
            )
            (simpleSymbolSentence (SymbolName "f") (SortName "S"))
        , updateAttributes
            ( Attributes
                [ Attribute.functionAttribute
                ]
            )
            (simpleSymbolSentence (SymbolName "g") (SortName "S"))
        , updateAttributes
            ( Attributes
                [ Attribute.functionAttribute
                , Attribute.constructorAttribute
                ]
            )
            (simpleSymbolSentence (SymbolName "p") (SortName "S"))
        , updateAttributes
            ( Attributes
                [ Attribute.functionAttribute
                , Attribute.constructorAttribute
                ]
            )
            (simpleSymbolSentence (SymbolName "q") (SortName "S"))
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                    externalize $
                        Validated.mkImplies
                            ( Validated.mkAnd
                                (Validated.mkTop sortVarS)
                                ( Validated.mkAnd
                                    ( Validated.mkIn
                                        sortVarS
                                        ( Validated.mkElemVar $
                                         mkElementVariable (testId "tVar") sortS
                                        )
                                        (Validated.mkApplySymbol tHead [])
                                    )
                                    (Validated.mkTop sortVarS)
                                )
                            )
                            ( Validated.mkAnd
                                ( Validated.mkEquals
                                    sortVarS
                                    ( Validated.mkApplySymbol
                                        (injHead sortS sortS)
                                        [ Validated.mkElemVar $
                                           mkElementVariable (testId "tVar") sortS
                                        ]
                                    )
                                    (Validated.mkApplySymbol sHead [])
                                )
                                (Validated.mkTop sortVarS)
                            )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                    externalize $
                       Validated.mkImplies
                            (Validated.mkTop sortVarS)
                            (Validated.mkAnd
                                (Validated.mkEquals
                                    sortVarS
                                    (Validated.mkApplySymbol gHead [])
                                    (Validated.mkApplySymbol sHead [])
                                )
                                (Validated.mkTop sortVarS)
                            )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                    externalize $
                       Validated.mkImplies
                            (Validated.mkTop sortVarS)
                            (Validated.mkAnd
                                (Validated.mkEquals
                                    sortVarS
                                    (Validated.mkApplySymbol fHead [])
                                    (Validated.mkTop sortS)
                                )
                                (Validated.mkTop sortVarS)
                            )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes =
                    Attributes [Attribute.priorityAttribute 2]
                , sentenceAxiomPattern =
                    externalize $
                       Validated.mkImplies
                            (Validated.mkTop sortVarS)
                            (Validated.mkAnd
                                (Validated.mkEquals
                                    sortVarS
                                    (Validated.mkApplySymbol fHead [])
                                    (Validated.mkApplySymbol sHead [])
                                )
                                (Validated.mkTop sortVarS)
                            )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes =
                    Attributes [Attribute.priorityAttribute 3]
                , sentenceAxiomPattern =
                    externalize $
                       Validated.mkImplies
                            (Validated.mkTop sortVarS)
                            (Validated.mkAnd
                                (Validated.mkEquals
                                    sortVarS
                                    (Validated.mkApplySymbol fHead [])
                                    (Validated.mkApplySymbol sHead [])
                                )
                                (Validated.mkTop sortVarS)
                            )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes =
                    Attributes [Attribute.owiseAttribute]
                , sentenceAxiomPattern =
                    externalize $
                       Validated.mkImplies
                            (Validated.mkTop sortVarS)
                            (Validated.mkAnd
                                (Validated.mkEquals
                                    sortVarS
                                    (Validated.mkApplySymbol fHead [])
                                    (Validated.mkApplySymbol tHead [])
                                )
                                (Validated.mkTop sortVarS)
                            )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes =
                    Attributes [Attribute.priorityAttribute 1]
                , sentenceAxiomPattern =
                    externalize $
                       Validated.mkImplies
                            (Validated.mkTop sortVarS)
                            (Validated.mkAnd
                                (Validated.mkEquals
                                    sortVarS
                                    (Validated.mkApplySymbol fHead [])
                                    (Validated.mkApplySymbol tHead [])
                                )
                                (Validated.mkTop sortVarS)
                            )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                    externalize $
                       Validated.mkImplies
                            (Validated.mkTop sortVarS)
                            (Validated.mkAnd
                                (Validated.mkEquals
                                    sortVarS
                                    (Validated.mkApplySymbol fHead [])
                                    (Validated.mkApplySymbol tHead [])
                                )
                                (Validated.mkTop sortVarS)
                            )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes = Attributes [simplificationAttribute Nothing]
                , sentenceAxiomPattern =
                    externalize $
                       Validated.mkImplies
                            (Validated.mkTop sortVarS)
                            (Validated.mkAnd
                                (Validated.mkEquals
                                    sortVarS
                                    (Validated.mkApplySymbol fHead [])
                                    (Validated.mkApplySymbol gHead [])
                                )
                                (Validated.mkTop sortVarS)
                            )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes =
                    Attributes
                        [ simplificationAttribute (Just 3)
                        ]
                , sentenceAxiomPattern =
                    externalize $
                       Validated.mkImplies
                            (Validated.mkTop sortVarS)
                            (Validated.mkAnd
                                (Validated.mkEquals
                                    sortVarS
                                    (Validated.mkApplySymbol pHead [])
                                    (Validated.mkApplySymbol qHead [])
                                )
                                (Validated.mkTop sortVarS)
                            )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes =
                    Attributes
                        [ simplificationAttribute (Just 1)
                        ]
                , sentenceAxiomPattern =
                    externalize $
                       Validated.mkImplies
                            (Validated.mkTop sortVarS)
                            (Validated.mkAnd
                                (Validated.mkEquals
                                    sortVarS
                                    (Validated.mkApplySymbol pHead [])
                                    (Validated.mkApplySymbol tHead [])
                                )
                                (Validated.mkTop sortVarS)
                            )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes =
                    Attributes
                        [ simplificationAttribute (Just 2)
                        ]
                , sentenceAxiomPattern =
                    externalize $
                       Validated.mkImplies
                            (Validated.mkTop sortVarS)
                            (Validated.mkAnd
                                (Validated.mkEquals
                                    sortVarS
                                    (Validated.mkApplySymbol pHead [])
                                    (Validated.mkApplySymbol qHead [])
                                )
                                (Validated.mkTop sortVarS)
                            )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                    externalize $
                       Validated.mkRewrites
                            (Validated.mkAnd (Validated.mkTop sortS) (Validated.mkApplySymbol fHead []))
                            (Validated.mkAnd (Validated.mkTop sortS) (Validated.mkApplySymbol tHead []))
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar, sortVar1]
                , sentenceAxiomAttributes = Attributes [simplificationAttribute Nothing]
                , sentenceAxiomPattern =
                    externalize $
                       Validated.mkImplies
                            (Validated.mkTop sortVarS)
                            (Validated.mkAnd
                                (Validated.mkEquals
                                    sortVarS
                                    (Validated.mkCeil sortVar1S (Validated.mkApplySymbol fHead []))
                                    (Validated.mkTop sortVar1S)
                                )
                                (Validated.mkTop sortVarS)
                            )
                }
        ]

testIndexedModule :: ValidatedModule Attribute.Symbol
testIndexedModule =
    let verifyResult = verifyAndIndexDefinition Builtin.koreVerifiers testDef
     in case verifyResult of
            Left err1 -> error (printError err1)
            Right indexedModules ->
                fromMaybe
                    (error "Module not found. Should not be possible.")
                    (Map.lookup (ModuleName "test") indexedModules)

testEvaluators :: BuiltinAndAxiomSimplifierMap
testEvaluators =
    mkEvaluatorRegistry $
        Map.map (fmap . Equation.mapVariables $ pure mkConfigVariable) $
            extractEquations testIndexedModule

testProcessedAxiomPatterns :: PartitionedEquationsMap
testProcessedAxiomPatterns =
    partitionEquations
        <$> Map.map
            (fmap . Equation.mapVariables $ pure mkConfigVariable)
            (extractEquations testIndexedModule)

testMetadataTools :: SmtMetadataTools Attribute.Symbol
testMetadataTools = MetadataTools.build testIndexedModule

testEnv :: Env (SimplifierT NoSMT)
testEnv =
    Mock.env
        { metadataTools = testMetadataTools
        , simplifierAxioms = testEvaluators
        }

test_functionRegistry :: [TestTree]
test_functionRegistry =
    [ testCase
        "Checking that a simplifier is found for f"
        ( let axiomId = AxiomIdentifier.Application (testId "f")
           in ( case Map.lookup axiomId testEvaluators of
                    Just _ -> return ()
                    _ -> assertFailure "Should find a simplifier for f"
              )
        )
    , testCase
        "Checking that a simplifier is found for parametric inj"
        ( let axiomId = AxiomIdentifier.Application (testId "inj")
           in ( case Map.lookup axiomId testEvaluators of
                    Just _ -> return ()
                    _ -> assertFailure "Should find a simplifier for inj"
              )
        )
    , testCase
        "Checking that a simplifier is found for ceil(f)"
        ( let axiomId =
                AxiomIdentifier.Ceil (AxiomIdentifier.Application (testId "f"))
           in ( case Map.lookup axiomId testEvaluators of
                    Just _ -> return ()
                    _ -> assertFailure "Should find a simplifier for ceil(f)"
              )
        )
    , testCase
        "Checking that evaluator map has size 4"
        ( assertEqual
            ""
            5
            (Map.size testEvaluators)
        )
    , testCase
        "Checking that the indexed module contains a rewrite axiom"
        ( assertEqual
            ""
            (1 :: Int)
            (length (extractRewriteAxioms testIndexedModule))
        )
    , testCase "Checking that evaluator simplifies correctly" $ do
        let expect = [mkApplySymbol sHead []]
        simplified <-
            runSimplifier testEnv $
                Pattern.simplify $
                    makePattern $ mkApplySymbol gHead []
        let actual = Pattern.term <$> toList simplified
        assertEqual "" expect actual
    , testCase "Checking that evaluator simplifies correctly" $ do
        let expect = [mkApplySymbol tHead []]
        simplified <-
            runSimplifier testEnv $
                Pattern.simplify $
                    makePattern $ mkApplySymbol pHead []
        let actual = Pattern.term <$> toList simplified
        assertEqual "" expect actual
    , testCase
        "Function rules sorted in order of priorities"
        ( let axiomId = AxiomIdentifier.Application (testId "f")
           in ( case Map.lookup axiomId testProcessedAxiomPatterns of
                    Just PartitionedEquations{functionRules} ->
                        assertEqual
                            ""
                            [1, 2, 3, defaultPriority, defaultPriority, owisePriority]
                            (fmap Equation.equationPriority functionRules)
                    _ -> assertFailure "Should find function rules for f"
              )
        )
    , testCase
        "Simplification rules sorted in order of priorities"
        ( let axiomId = AxiomIdentifier.Application (testId "p")
           in ( case Map.lookup axiomId testProcessedAxiomPatterns of
                    Just PartitionedEquations{simplificationRules} ->
                        assertEqual
                            ""
                            [1, 2, 3]
                            (fmap Equation.equationPriority simplificationRules)
                    _ -> assertFailure "Should find simplification rules for p"
              )
        )
    ]
  where
    makePattern :: TermLike RewritingVariableName -> Pattern RewritingVariableName
    makePattern = Pattern.fromTermLike
