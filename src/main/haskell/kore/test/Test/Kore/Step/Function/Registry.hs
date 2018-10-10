module Test.Kore.Step.Function.Registry (test_functionRegistry) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )
import           Data.Proxy
                 ( Proxy (..) )

import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( groundHead )
import           Kore.AST.PureToKore
                 ( patternPureToKore )
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Builtin as Builtin
import           Kore.Error
                 ( printError )
import           Kore.IndexedModule.IndexedModule
                 ( KoreIndexedModule )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), extractMetadataTools )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.AxiomPatterns
                 ( koreIndexedModuleToAxiomPatterns )
import           Kore.Step.ExpandedPattern
                 ( CommonExpandedPattern, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator )
import           Kore.Step.Function.Registry
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Simplification.Simplifier as Simplifier
                 ( create )
import           Kore.Step.StepperAttributes

import Test.Kore.ASTVerifier.DefinitionVerifier
import Test.Kore.Comparators ()

updateAttributes :: Attributes -> KoreSentence -> KoreSentence
updateAttributes attrs = applyUnifiedSentence updateAttrs updateAttrs
  where
    updateAttrs
        :: MetaOrObject level
        => Sentence level UnifiedSortVariable UnifiedPattern Variable
        -> KoreSentence
    updateAttrs (SentenceSymbolSentence ss) =
        constructUnifiedSentence SentenceSymbolSentence
            (ss { sentenceSymbolAttributes = attrs })
    updateAttrs _ = error "unsupported non-symbol sentence"

sortVar :: SortVariable Object
sortVar = SortVariable (testId "R")

sortVarS :: Sort Object
sortVarS = SortVariableSort sortVar

sortS :: Sort level
sortS = SortActualSort (SortActual (testId "S") [])

fHead, gHead, sHead, tHead :: SymbolOrAlias level
fHead = groundHead "f" AstLocationTest
gHead = groundHead "g" AstLocationTest
sHead = groundHead "s" AstLocationTest
tHead = groundHead "t" AstLocationTest

testDef :: KoreDefinition
testDef = simpleDefinitionFromSentences
            (ModuleName "test")
            [ simpleSortSentence (SortName "S")
            , simpleObjectSymbolSentence (SymbolName "s") (SortName "S")
            , simpleObjectSymbolSentence (SymbolName "t") (SortName "S")
            , updateAttributes
                (Attributes [functionAttribute, constructorAttribute])
                (simpleObjectSymbolSentence (SymbolName "f") (SortName "S"))
            , updateAttributes
                (Attributes [functionAttribute, constructorAttribute])
                (simpleObjectSymbolSentence (SymbolName "g") (SortName "S"))
            , asSentence
                (SentenceAxiom
                    { sentenceAxiomParameters = [asUnified sortVar]
                    , sentenceAxiomAttributes = Attributes []
                    , sentenceAxiomPattern =
                        (patternPureToKore
                            ( Implies_ sortVarS
                                (Top_ sortVarS)
                                (And_ sortVarS
                                    (Equals_ sortS sortVarS
                                        (App_ gHead [])
                                        (App_ sHead [])
                                    )
                                    (Top_ sortVarS)
                                )
                            :: CommonPurePattern Object)
                        )
                    }
                ::KoreSentenceAxiom)
            , asSentence
                (SentenceAxiom
                    { sentenceAxiomParameters = [asUnified sortVar]
                    , sentenceAxiomAttributes = Attributes []
                    , sentenceAxiomPattern =
                        (patternPureToKore
                            ( Implies_ sortVarS
                                (Top_ sortVarS)
                                (And_ sortVarS
                                    (Equals_ sortS sortVarS
                                        (Top_ sortS)
                                        (App_ fHead [])
                                    )
                                    (Top_ sortVarS)
                                )
                            :: CommonPurePattern Object)
                        )
                    }
                ::KoreSentenceAxiom)
            , asSentence
                (SentenceAxiom
                    { sentenceAxiomParameters = [asUnified sortVar]
                    , sentenceAxiomAttributes = Attributes []
                    , sentenceAxiomPattern =
                        (patternPureToKore
                            ( Implies_ sortVarS
                                (Top_ sortVarS)
                                (And_ sortVarS
                                    (Equals_ sortS sortVarS
                                        (App_ fHead [])
                                        (App_ sHead [])
                                    )
                                    (Top_ sortVarS)
                                )
                            :: CommonPurePattern Object)
                        )
                    }
                ::KoreSentenceAxiom)
             , asSentence
                (SentenceAxiom
                    { sentenceAxiomParameters = [asUnified sortVar]
                    , sentenceAxiomAttributes = Attributes []
                    , sentenceAxiomPattern =
                        (patternPureToKore
                            ( Implies_ sortVarS
                                (Top_ sortVarS)
                                (And_ sortVarS
                                    (Equals_ sortS sortVarS
                                        (App_ fHead [])
                                        (App_ tHead [])
                                    )
                                    (Top_ sortVarS)
                                )
                            :: CommonPurePattern Object)
                        )
                    }
                ::KoreSentenceAxiom)
            , asSentence
                (SentenceAxiom
                    { sentenceAxiomParameters = [asUnified sortVar]
                    , sentenceAxiomAttributes = Attributes []
                    , sentenceAxiomPattern =
                        (patternPureToKore
                            (Top_ sortS
                            :: CommonPurePattern Object)
                        )
                    }
                ::KoreSentenceAxiom)
            , asSentence
                (SentenceAxiom
                    { sentenceAxiomParameters = [asUnified sortVar]
                    , sentenceAxiomAttributes = Attributes []
                    , sentenceAxiomPattern =
                        (patternPureToKore
                            (And_ sortS (Top_ sortS)
                                (And_ sortS (Top_ sortS)
                                    (Rewrites_ sortS
                                        (App_ fHead [])
                                        (App_ tHead [])
                                    )
                                )
                            :: CommonPurePattern Object)
                        )
                    }
                ::KoreSentenceAxiom)
            ]

testIndexedModule :: KoreIndexedModule StepperAttributes
testIndexedModule =
    let
        attributesVerification = defaultAttributesVerification Proxy
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

testId :: String -> Id level
testId name =
    Id
        { getId = name
        , idLocation = AstLocationTest
        }

testEvaluators
    :: Map.Map (Id Object) [ApplicationFunctionEvaluator Object]
testEvaluators = extractEvaluators Object testIndexedModule

testMetadataTools :: MetadataTools Object StepperAttributes
testMetadataTools = extractMetadataTools testIndexedModule

test_functionRegistry :: [TestTree]
test_functionRegistry =
    [ testCase "Checking that two axioms are found for f"
        (assertEqual ""
            2
            (length $ fromMaybe
                (error "Should find precisely two axioms for f")
                (Map.lookup (testId "f") testEvaluators)
            )
        )
     , testCase "Checking that evaluator map has size 2"
        (assertEqual ""
            2
            (Map.size testEvaluators)
        )
    , testCase "Checking that the indexed module contains a rewrite axiom"
        (assertEqual ""
            (1::Int)
            (length (koreIndexedModuleToAxiomPatterns Object testIndexedModule))
        )
    , testCase "Checking that evaluator simplifies correctly"
        (assertEqual ""
            (App_ sHead [])
            ( ExpandedPattern.term
            $ head $ OrOfExpandedPattern.extractPatterns $ fst
            $ evalSimplifier
            $ ExpandedPattern.simplify
                testMetadataTools
                (Simplifier.create testMetadataTools testEvaluators)
                (makeExpandedPattern (App_ gHead []))
            )
        )
    ]
  where
    makeExpandedPattern
        :: CommonPurePattern Object
        -> CommonExpandedPattern Object
    makeExpandedPattern pat =
        Predicated
        { term = pat
        , predicate = makeTruePredicate
        , substitution = []
        }
