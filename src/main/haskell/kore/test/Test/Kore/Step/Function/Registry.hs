module Test.Kore.Step.Function.Registry (test_functionRegistry) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( assertEqual, testCase )

import qualified Data.Map as Map
import           Data.Maybe
                 ( isJust )
import           Data.Proxy
                 ( Proxy (..) )

import           Kore.AST.Common
import           Kore.AST.Kore
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( CommonPurePattern, groundHead )
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
import           Kore.Step.Function.Data
                 ( CommonApplicationFunctionEvaluator )
import           Kore.Step.Function.Registry
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

fHead, sHead :: SymbolOrAlias level
fHead = groundHead "f" AstLocationTest
sHead = groundHead "s" AstLocationTest

testDef :: KoreDefinition
testDef = simpleDefinitionFromSentences
            (ModuleName "test")
            [ simpleSortSentence (SortName "S")
            , simpleObjectSymbolSentence (SymbolName "s") (SortName "S")
            , simpleObjectSymbolSentence (SymbolName "t") (SortName "S")
            , updateAttributes
                (Attributes [functionAttribute, constructorAttribute])
                (simpleObjectSymbolSentence (SymbolName "f") (SortName "S"))
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
                    }::KoreSentenceAxiom
                )
            ]

testIndexedModule :: KoreIndexedModule StepperAttributes
testIndexedModule =
    let
        attributesVerification = defaultAttributesVerification Proxy
        verifyResult = verifyAndIndexDefinition
            attributesVerification
            Builtin.koreBuiltins
            testDef
    in
        case verifyResult of
            Left err1            -> error (printError err1)
            Right indexedModules ->
                case Map.lookup (ModuleName "test") indexedModules of
                    Nothing ->
                        error
                            (  "The main module, '"
                            ++ "test"
                            ++ "', was not found. Check the --module flag."
                            )
                    Just m -> m

testId :: String -> Id level
testId name =
    Id
        { getId = name
        , idLocation = AstLocationTest
        }

testEvaluators
    :: Map.Map (Id Object) [CommonApplicationFunctionEvaluator Object]
testEvaluators = extractEvaluators Object testIndexedModule

test_functionRegistry :: [TestTree]
test_functionRegistry =
    [ testCase "Checking that axiom is found"
        (assertEqual ""
            True
            (isJust
                (Map.lookup (testId "f") testEvaluators)
            )
        )
    ]
