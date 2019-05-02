module Test.Kore.Attribute.Overload where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Map.Strict as Map
import           Data.Proxy

import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.Attribute.Overload
import qualified Kore.Builtin as Builtin
import           Kore.Internal.TermLike
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import           Kore.Step.Axiom.Registry
import           Kore.Syntax.Definition
import           Kore.Syntax.Pattern as Pure

import           Test.Kore
import           Test.Kore.Attribute.Parser
import           Test.Kore.Builtin.Definition
                 ( sortDecl, symbolDecl )
import qualified Test.Kore.Step.MockSymbols as Mock

parseOverload :: Attributes -> Parser Overload
parseOverload = parseAttributes

superId :: Id
superId = testId "super"

superSymbol :: SymbolOrAlias
superSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = superId
        , symbolOrAliasParams = []
        }

subId :: Id
subId = testId "sub"

subSymbol :: SymbolOrAlias
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
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias = overloadSymbol
                , applicationChildren =
                    [ (asAttributePattern . StringLiteralF)
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
        (asAttributePattern . ApplicationF)
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
        axiomPatternsToEvaluators $ extractEqualityAxioms indexedModule
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

    overloadAxiom :: ParsedSentence
    overloadAxiom =
        SentenceAxiomSentence SentenceAxiom
            { sentenceAxiomParameters = [ sortVarS ]
            , sentenceAxiomAttributes =
                Attributes [ overloadAttribute superSymbol subSymbol ]
            , sentenceAxiomPattern =
                Pure.eraseAnnotations
                $ mkEquals sortS
                    (mkApp Mock.testSort superSymbol [])
                    (mkApp Mock.testSort subSymbol   [])
            }
      where
        sortVarS = SortVariable "S"
        sortS = SortVariableSort sortVarS
