module Test.Kore.Step.Axiom.Registry (test_functionRegistry) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, assertFailure, testCase )

import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )
import           Data.Proxy
                 ( Proxy (..) )

import           Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Simplification
                 ( simplificationSymbol )
import           Kore.Attribute.Symbol
import qualified Kore.Builtin as Builtin
import           Kore.Error
                 ( printError )
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import qualified Kore.IndexedModule.MetadataToolsBuilder as MetadataTools
                 ( build )
import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Step.Axiom.Data
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
                 ( AxiomIdentifier (..) )
import           Kore.Step.Axiom.Registry
import           Kore.Step.Rule
                 ( extractRewriteAxioms )
import           Kore.Step.Simplification.Data
                 ( Env (..), evalSimplifier )
import qualified Kore.Step.Simplification.Pattern as Pattern
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Syntax.PatternF
                 ( groundHead )
import qualified SMT

import           Test.Kore
import           Test.Kore.ASTVerifier.DefinitionVerifier
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock

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

fHead, gHead, sHead, tHead :: SymbolOrAlias
fHead = groundHead "f" AstLocationTest
gHead = groundHead "g" AstLocationTest
sHead = groundHead "s" AstLocationTest
tHead = groundHead "t" AstLocationTest
injHead :: Sort -> Sort -> SymbolOrAlias
injHead s1 s2 = SymbolOrAlias
    { symbolOrAliasConstructor = testId "inj"
    , symbolOrAliasParams = [s1, s2]
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
            (Attributes [functionAttribute, constructorAttribute])
            (simpleSymbolSentence (SymbolName "f") (SortName "S"))
        , updateAttributes
            (Attributes [functionAttribute, constructorAttribute])
            (simpleSymbolSentence (SymbolName "g") (SortName "S"))
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalizePattern $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals
                            sortVarS
                            (mkApp sortS (injHead sortS sortS)
                                [mkApp sortS tHead []]
                            )
                            (mkApp sortS sHead [])
                        )
                        (mkTop sortVarS)
                    )
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalizePattern $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals
                            sortVarS
                            (mkApp sortS gHead [])
                            (mkApp sortS sHead [])
                        )
                        (mkTop sortVarS)
                    )
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalizePattern $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals sortVarS
                            (mkTop sortS)
                            (mkApp sortS fHead [])
                        )
                        (mkTop sortVarS)
                    )
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalizePattern $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals sortVarS
                            (mkApp sortS fHead [])
                            (mkApp sortS sHead [])
                        )
                        (mkTop sortVarS)
                    )
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalizePattern $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals sortVarS
                            (mkApp sortS fHead [])
                            (mkApp sortS tHead [])
                        )
                        (mkTop sortVarS)
                    )
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes =
                Attributes [ attributePattern_ simplificationSymbol ]
            , sentenceAxiomPattern =
                Builtin.externalizePattern $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals sortVarS
                            (mkApp sortS fHead [])
                            (mkApp sortS gHead [])
                        )
                        (mkTop sortVarS)
                    )
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalizePattern $ mkTop sortS
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalizePattern $ mkRewrites
                    (mkAnd mkTop_ (mkApp sortS fHead []))
                    (mkAnd mkTop_ (mkApp sortS tHead []))
            }
        , SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [sortVar, sortVar1]
            , sentenceAxiomAttributes = Attributes []
            , sentenceAxiomPattern =
                Builtin.externalizePattern $ mkImplies
                    (mkTop sortVarS)
                    (mkAnd
                        (mkEquals sortVarS
                            (mkCeil sortVar1S (mkApp sortS fHead []))
                            mkTop_
                        )
                        (mkTop sortVarS)
                    )
            }
        ]

testIndexedModule :: VerifiedModule StepperAttributes Attribute.Axiom
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

testEvaluators
    :: BuiltinAndAxiomSimplifierMap
testEvaluators =
    axiomPatternsToEvaluators $ extractEqualityAxioms testIndexedModule

testMetadataTools :: SmtMetadataTools StepperAttributes
testMetadataTools = MetadataTools.build testIndexedModule

testEnv :: Env
testEnv = Env { metadataTools = testMetadataTools }

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
        let expect = mkApp sortS sHead []
        simplified <-
            SMT.runSMT SMT.defaultConfig emptyLogger
            $ evalSimplifier testEnv
            $ Pattern.simplify
                Mock.substitutionSimplifier
                (Simplifier.create testEvaluators)
                testEvaluators
                (makePattern (mkApp sortS gHead []))
        let actual =
                Pattern.term $ head
                $ MultiOr.extractPatterns simplified
        assertEqual "" expect actual
    ]
  where
    makePattern :: TermLike Variable -> Pattern Variable
    makePattern = Pattern.fromTermLike
