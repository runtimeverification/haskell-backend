module Test.Kore.Attribute.Overload where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map.Strict as Map
import           Data.Proxy

import           Kore.AST.Kore
import qualified Kore.AST.Pure as Pure
import           Kore.AST.PureToKore
import           Kore.AST.Sentence
import           Kore.AST.Valid
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.Attribute.Overload
import qualified Kore.Builtin as Builtin
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import           Kore.Step.Axiom.Registry

import           Test.Kore
import           Test.Kore.Attribute.Parser
import           Test.Kore.Builtin.Definition
                 ( sortDecl, symbolDecl )
import qualified Test.Kore.Step.MockSymbols as Mock

parseOverload :: Attributes -> Parser Overload
parseOverload = parseAttributes

superId :: Id Object
superId = testId "super"

superSymbol :: SymbolOrAlias Object
superSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = superId
        , symbolOrAliasParams = []
        }

subId :: Id Object
subId = testId "sub"

subSymbol :: SymbolOrAlias Object
subSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = subId
        , symbolOrAliasParams = []
        }

test_Overload :: TestTree
test_Overload =
    testCase "[overload{}(super{}(), sub{}())] :: Overload"
    $ expectSuccess Overload { getOverload = Just (superSymbol, subSymbol) }
    $ parseOverload $ Attributes [ overloadAttribute superSymbol subSymbol ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[overload{}(super{}(), sub{}())] :: Attributes"
    $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ overloadAttribute superSymbol subSymbol ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[overload{}(_, _), overload{}(_, _)]"
    $ expectFailure
    $ parseOverload
    $ Attributes
        [ overloadAttribute superSymbol subSymbol
        , overloadAttribute superSymbol subSymbol
        ]

test_arguments :: TestTree
test_arguments =
    testCase "[overload{}(\"illegal\")]"
    $ expectFailure
    $ parseOverload $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asCommonKorePattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias = overloadSymbol
                , applicationChildren =
                    [ (asCommonKorePattern . StringLiteralPattern)
                        (StringLiteral "illegal")
                    ]
                }

test_parameters :: TestTree
test_parameters =
    testCase "[overload{illegal}()]"
    $ expectFailure
    $ parseOverload $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asCommonKorePattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = overloadId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }

test_ignore :: TestTree
test_ignore =
    testCase "Ignore overloaded production axioms" $
        case Map.lookup (AxiomIdentifier.Application superId) evaluators of
            Nothing -> return ()
            Just _ -> assertFailure "Should ignore overloaded production axiom"
  where
    evaluators =
        axiomPatternsToEvaluators $ extractEqualityAxioms Object indexedModule
      where
        Just indexedModule = Map.lookup testModuleName verifiedModules
          where
            Right verifiedModules =
                verifyAndIndexDefinition
                    attributesVerification
                    Builtin.koreVerifiers
                    testDefinition
            attributesVerification = defaultAttributesVerification Proxy Proxy

    testDefinition =
        Definition
            { definitionAttributes = Attributes []
            , definitionModules = [ testModule ]
            }

    testModuleName = ModuleName "test"
    testModule =
        Module
            { moduleName = testModuleName
            , moduleAttributes = Attributes []
            , moduleSentences =
                [ sortDecl   Mock.testSort
                , symbolDecl superSymbol Mock.testSort [] []
                , symbolDecl subSymbol   Mock.testSort [] []
                , overloadAxiom
                ]
            }

    overloadAxiom :: KoreSentence
    overloadAxiom =
        asKoreAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [ UnifiedObject sortVarS ]
            , sentenceAxiomAttributes =
                Attributes [ overloadAttribute superSymbol subSymbol ]
            , sentenceAxiomPattern =
                patternPureToKore
                $ Pure.eraseAnnotations
                $ mkEquals sortS
                    (mkApp Mock.testSort superSymbol [])
                    (mkApp Mock.testSort subSymbol   [])
            }
      where
        sortVarS = SortVariable "S"
        sortS = SortVariableSort sortVarS
