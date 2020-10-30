module Test.Kore.Attribute.Symbol.Symbolic
    ( test_symbolic
    , test_Attributes
    , test_duplicate
    , test_arguments
    , test_parameters
    ) where

import Prelude.Kore

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Symbol.Symbolic
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseSymbolic :: Attributes -> Parser Symbolic
parseSymbolic = parseAttributes

test_symbolic :: TestTree
test_symbolic =
    testCase "[symbolic{}}()] :: Symbolic"
        $ expectSuccess Symbolic { isSymbolic = True }
        $ parseSymbolic $ Attributes [ symbolicAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[symbolic{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ symbolicAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[symbolic{}(), symbolic{}()]"
        $ expectFailure $ parseSymbolic
        $ Attributes [ symbolicAttribute, symbolicAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[symbolic{}(\"illegal\")]"
        $ expectFailure
        $ parseSymbolic $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern symbolicSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[symbolic{illegal}()]"
        $ expectFailure
        $ parseSymbolic $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = symbolicId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
