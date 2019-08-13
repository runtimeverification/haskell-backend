module Test.Kore.Attribute.Symbol.Anywhere where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Symbol.Anywhere
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseAnywhere :: Attributes -> Parser Anywhere
parseAnywhere = parseAttributes

test_anywhere :: TestTree
test_anywhere =
    testCase "[anywhere{}()] :: Anywhere"
        $ expectSuccess Anywhere { isAnywhere = True }
        $ parseAnywhere $ Attributes [ anywhereAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[anywhere{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ anywhereAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[anywhere{}(), anywhere{}()]"
        $ expectFailure $ parseAnywhere
        $ Attributes [ anywhereAttribute, anywhereAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[anywhere{}(\"illegal\")]"
        $ expectFailure
        $ parseAnywhere $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern anywhereSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[anywhere{illegal}()]"
        $ expectFailure
        $ parseAnywhere $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = anywhereId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
