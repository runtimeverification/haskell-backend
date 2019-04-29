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

import           Kore.AST.Common
                 ( Application (..) )
import qualified Kore.AST.Common as Common
import           Kore.AST.Pure
                 ( groundHead )
import           Kore.AST.Sentence
import           Kore.AST.Valid
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
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Sort
import           Kore.Step.Axiom.Data
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
                 ( AxiomIdentifier (..) )
import           Kore.Step.Axiom.Registry
import           Kore.Step.Pattern as Pattern
import qualified Kore.Step.Representation.MultiOr as MultiOr
import           Kore.Step.Rule
                 ( extractRewriteAxioms )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import qualified Kore.Step.Simplification.Pattern as Pattern
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.TermLike
import qualified Kore.Verified as Verified
import qualified SMT

import           Test.Kore
import           Test.Kore.ASTVerifier.DefinitionVerifier
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock

updateAttributes :: Attributes -> Verified.Sentence -> Verified.Sentence
updateAttributes attrs = updateAttrs
  where
    updateAttrs :: Verified.Sentence -> Verified.Sentence
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

fHead, gHead, sHead, tHead :: SymbolOrAlias level
fHead = groundHead "f" AstLocationTest
gHead = groundHead "g" AstLocationTest
sHead = groundHead "s" AstLocationTest
tHead = groundHead "t" AstLocationTest
injHead :: Sort -> Sort -> SymbolOrAlias level
injHead s1 s2 = SymbolOrAlias
    { symbolOrAliasConstructor = testId "inj"
    , symbolOrAliasParams = [s1, s2]
    }


testDef :: Definition Verified.Sentence
testDef =
    simpleDefinitionFromSentences
        (ModuleName "test")
        [ simpleSortSentence (SortName "S")
        , simpleObjectSymbolSentence (SymbolName "s") (SortName "S")
        , simpleObjectSymbolSentence (SymbolName "t") (SortName "S")
        , objectSymbolSentenceWithParametersAndArguments
            (SymbolName "inj")
            [sortVar, sortVar1]
            sortVar1S
            [sortVarS]
        , updateAttributes
            (Attributes [functionAttribute, constructorAttribute])
            (simpleObjectSymbolSentence (SymbolName "f") (SortName "S"))
        , updateAttributes
            (Attributes [functionAttribute, constructorAttribute])
            (simpleObjectSymbolSentence (SymbolName "g") (SortName "S"))
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                        (mkImplies
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
                        )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                        (mkImplies
                            (mkTop sortVarS)
                            (mkAnd
                                (mkEquals
                                    sortVarS
                                    (mkApp sortS gHead [])
                                    (mkApp sortS sHead [])
                                )
                                (mkTop sortVarS)
                            )
                        )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                        (mkImplies
                            (mkTop sortVarS)
                            (mkAnd
                                (mkEquals sortVarS
                                    (mkTop sortS)
                                    (mkApp sortS fHead [])
                                )
                                (mkTop sortVarS)
                            )
                        )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                        (mkImplies
                            (mkTop sortVarS)
                            (mkAnd
                                (mkEquals sortVarS
                                    (mkApp sortS fHead [])
                                    (mkApp sortS sHead [])
                                )
                                (mkTop sortVarS)
                            )
                        :: TermLike Variable)
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                        (mkImplies
                            (mkTop sortVarS)
                            (mkAnd
                                (mkEquals sortVarS
                                    (mkApp sortS fHead [])
                                    (mkApp sortS tHead [])
                                )
                                (mkTop sortVarS)
                            )
                        :: TermLike Variable)
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes =
                    Attributes
                        [ asParsedPattern
                            (Common.ApplicationPattern Application
                                { applicationSymbolOrAlias =
                                    simplificationSymbol
                                , applicationChildren = []
                                }
                            )
                        ]
                , sentenceAxiomPattern =
                        (mkImplies
                            (mkTop sortVarS)
                            (mkAnd
                                (mkEquals sortVarS
                                    (mkApp sortS fHead [])
                                    (mkApp sortS gHead [])
                                )
                                (mkTop sortVarS)
                            )
                        :: TermLike Variable)
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                        (mkTop sortS :: TermLike Variable)
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                        (mkRewrites
                            (mkAnd mkTop_ (mkApp sortS fHead []))
                            (mkAnd mkTop_ (mkApp sortS tHead []))
                        )
                }
        , SentenceAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters =
                    [sortVar, sortVar1]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                        (mkImplies
                            (mkTop sortVarS)
                            (mkAnd
                                (mkEquals sortVarS
                                    (mkCeil sortVar1S (mkApp sortS fHead []))
                                    mkTop_
                                )
                                (mkTop sortVarS)
                            )
                        :: TermLike Variable)
                }
        ]

testIndexedModule :: VerifiedModule StepperAttributes Attribute.Axiom
testIndexedModule =
    let
        attributesVerification = defaultAttributesVerification Proxy Proxy
        verifyResult = verifyAndIndexDefinition
            attributesVerification
            Builtin.koreVerifiers
            (eraseSentenceAnnotations <$> testDef)
    in
        case verifyResult of
            Left err1            -> error (printError err1)
            Right indexedModules ->
                fromMaybe
                    (error "Module not found. Should not be possible.")
                    (Map.lookup (ModuleName "test") indexedModules)

testEvaluators
    :: BuiltinAndAxiomSimplifierMap Object
testEvaluators =
    axiomPatternsToEvaluators $ extractEqualityAxioms testIndexedModule

testMetadataTools :: SmtMetadataTools StepperAttributes
testMetadataTools = MetadataTools.build testIndexedModule

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
        (simplified, _) <-
            SMT.runSMT SMT.defaultConfig
            $ evalSimplifier emptyLogger
            $ Pattern.simplify
                testMetadataTools
                (Mock.substitutionSimplifier testMetadataTools)
                (Simplifier.create testMetadataTools testEvaluators)
                testEvaluators
                (makePattern (mkApp sortS gHead []))
        let actual =
                Pattern.term $ head
                $ MultiOr.extractPatterns simplified
        assertEqual "" expect actual
    ]
  where
    makePattern
        :: TermLike Variable
        -> Pattern Object Variable
    makePattern pat =
        Conditional
        { term = pat
        , predicate = makeTruePredicate
        , substitution = mempty
        }
