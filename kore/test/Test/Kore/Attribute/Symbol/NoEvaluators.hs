module Test.Kore.Attribute.Symbol.NoEvaluators
    ( test_noEvaluators
    , test_Attributes
    , test_duplicate
    , test_arguments
    , test_parameters
    )where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Symbol.NoEvaluators
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseNoEvaluators :: Attributes -> Parser NoEvaluators
parseNoEvaluators = parseAttributes

test_noEvaluators :: TestTree
test_noEvaluators =
    testCase "[noEvaluators{}()] :: NoEvaluators"
        $ expectSuccess NoEvaluators { hasNoEvaluators = True }
        $ parseNoEvaluators $ Attributes [ noEvaluatorsAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[noEvaluators{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ noEvaluatorsAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[noEvaluators{}(), noEvaluators{}()]"
        $ expectFailure $ parseNoEvaluators
        $ Attributes [ noEvaluatorsAttribute, noEvaluatorsAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[noEvaluators{}(\"illegal\")]"
        $ expectFailure
        $ parseNoEvaluators $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern noEvaluatorsSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[noEvaluators{illegal}()]"
        $ expectFailure
        $ parseNoEvaluators $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = noEvaluatorsId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
