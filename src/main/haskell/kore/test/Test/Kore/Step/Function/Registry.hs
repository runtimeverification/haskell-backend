module Test.Kore.Step.Function.Registry (test_functionRegistry) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, assertFailure, testCase )

import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Text
                 ( Text )

import           Kore.AST.Kore
import           Kore.AST.Pure
import           Kore.AST.Sentence
import           Kore.AST.Valid
import           Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Attribute.Axiom as Attribute
import           Kore.Attribute.Simplification
                 ( simplificationSymbol )
import qualified Kore.Builtin as Builtin
import           Kore.Error
                 ( printError )
import           Kore.IndexedModule.IndexedModule
                 ( VerifiedModule )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), extractMetadataTools )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.AxiomPatterns
                 ( extractRewriteAxioms )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Data
import qualified Kore.Step.Function.Identifier as AxiomIdentifier
                 ( AxiomIdentifier (..) )
import           Kore.Step.Function.Registry
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes
import qualified SMT

import           Test.Kore
                 ( emptyLogger, noRepl )
import           Test.Kore.ASTVerifier.DefinitionVerifier
import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSimplifiers as Mock

updateAttributes :: Attributes -> VerifiedKoreSentence -> VerifiedKoreSentence
updateAttributes attrs = applyUnifiedSentence updateAttrs updateAttrs
  where
    updateAttrs
        :: MetaOrObject level
        => Sentence level UnifiedSortVariable VerifiedKorePattern
        -> VerifiedKoreSentence
    updateAttrs (SentenceSymbolSentence ss) =
        constructUnifiedSentence SentenceSymbolSentence
            (ss { sentenceSymbolAttributes = attrs })
    updateAttrs _ = error "unsupported non-symbol sentence"

sortVar :: SortVariable Object
sortVar = SortVariable (testId "R")

sortVar1 :: SortVariable Object
sortVar1 = SortVariable (testId "R1")

sortVarS :: Sort Object
sortVarS = SortVariableSort sortVar

sortVar1S :: Sort Object
sortVar1S = SortVariableSort sortVar1

sortS :: Sort level
sortS = SortActualSort (SortActual (testId "S") [])

fHead, gHead, sHead, tHead :: SymbolOrAlias level
fHead = groundHead "f" AstLocationTest
gHead = groundHead "g" AstLocationTest
sHead = groundHead "s" AstLocationTest
tHead = groundHead "t" AstLocationTest
injHead :: Sort level -> Sort level -> SymbolOrAlias level
injHead s1 s2 = SymbolOrAlias
    { symbolOrAliasConstructor = Id
        { getId = "inj"
        , idLocation = AstLocationTest
        }
    , symbolOrAliasParams = [s1, s2]
    }


testDef :: VerifiedKoreDefinition
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
        , asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [asUnified sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                    toKorePattern
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
        , asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [asUnified sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                    toKorePattern
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
        , asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [asUnified sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                    toKorePattern
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
        , asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [asUnified sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkImplies
                            (mkTop sortVarS)
                            (mkAnd
                                (mkEquals sortVarS
                                    (mkApp sortS fHead [])
                                    (mkApp sortS sHead [])
                                )
                                (mkTop sortVarS)
                            )
                        :: CommonStepPattern Object)
                }
        , asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [asUnified sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkImplies
                            (mkTop sortVarS)
                            (mkAnd
                                (mkEquals sortVarS
                                    (mkApp sortS fHead [])
                                    (mkApp sortS tHead [])
                                )
                                (mkTop sortVarS)
                            )
                        :: CommonStepPattern Object)
                }
        , asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [asUnified sortVar]
                , sentenceAxiomAttributes =
                    Attributes
                        [ asCommonKorePattern
                            (ApplicationPattern Application
                                { applicationSymbolOrAlias =
                                    simplificationSymbol
                                , applicationChildren = []
                                }
                            )
                        ]
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkImplies
                            (mkTop sortVarS)
                            (mkAnd
                                (mkEquals sortVarS
                                    (mkApp sortS fHead [])
                                    (mkApp sortS gHead [])
                                )
                                (mkTop sortVarS)
                            )
                        :: CommonStepPattern Object)
                }
        , asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [asUnified sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkTop sortS :: CommonStepPattern Object)
                }
        , asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters = [asUnified sortVar]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkRewrites
                            (mkAnd mkTop_ (mkApp sortS fHead []))
                            (mkAnd mkTop_ (mkApp sortS tHead []))
                        )
                }
        , asKoreAxiomSentence
            SentenceAxiom
                { sentenceAxiomParameters =
                    [asUnified sortVar, asUnified sortVar1]
                , sentenceAxiomAttributes = Attributes []
                , sentenceAxiomPattern =
                    toKorePattern
                        (mkImplies
                            (mkTop sortVarS)
                            (mkAnd
                                (mkEquals sortVarS
                                    (mkCeil sortVar1S (mkApp sortS fHead []))
                                    mkTop_
                                )
                                (mkTop sortVarS)
                            )
                        :: CommonStepPattern Object)
                }
        ]

testIndexedModule :: VerifiedModule StepperAttributes Attribute.Axiom
testIndexedModule =
    let
        attributesVerification = defaultAttributesVerification Proxy Proxy
        verifyResult = verifyAndIndexDefinition
            attributesVerification
            Builtin.koreVerifiers
            (eraseUnifiedSentenceAnnotations <$> testDef)
    in
        case verifyResult of
            Left err1            -> error (printError err1)
            Right indexedModules ->
                fromMaybe
                    (error "Module not found. Should not be possible.")
                    (Map.lookup (ModuleName "test") indexedModules)

testId :: Text -> Id level
testId name =
    Id
        { getId = name
        , idLocation = AstLocationTest
        }

testEvaluators
    :: BuiltinAndAxiomSimplifierMap Object
testEvaluators =
    axiomPatternsToEvaluators
    $ extractFunctionAxioms Object testIndexedModule

testMetadataTools :: MetadataTools Object StepperAttributes
testMetadataTools = extractMetadataTools testIndexedModule

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
            (length (extractRewriteAxioms Object testIndexedModule))
        )
    , testCase "Checking that evaluator simplifies correctly" $ do
        let expect = mkApp sortS sHead []
        (simplified, _) <-
            SMT.runSMT SMT.defaultConfig
            $ evalSimplifier emptyLogger noRepl
            $ ExpandedPattern.simplify
                testMetadataTools
                (Mock.substitutionSimplifier testMetadataTools)
                (Simplifier.create testMetadataTools testEvaluators)
                (makeExpandedPattern (mkApp sortS gHead []))
        let actual =
                ExpandedPattern.term $ head
                $ OrOfExpandedPattern.extractPatterns simplified
        assertEqual "" expect actual
    ]
  where
    makeExpandedPattern
        :: CommonStepPattern Object
        -> CommonExpandedPattern Object
    makeExpandedPattern pat =
        Predicated
        { term = pat
        , predicate = makeTruePredicate
        , substitution = mempty
        }
