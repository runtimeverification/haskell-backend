module Test.Kore.Attribute.Trusted where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Trusted
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseTrusted :: Attributes -> Parser Trusted
parseTrusted = parseAttributes

test_trusted :: TestTree
test_trusted =
    testCase "[trusted{}()] :: Trusted"
        $ expectSuccess Trusted { isTrusted = True }
        $ parseTrusted $ Attributes [ trustedAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[trusted{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ trustedAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[trusted{}(), trusted{}()]"
        $ expectFailure
        $ parseTrusted $ Attributes [ trustedAttribute, trustedAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[trusted{}(\"illegal\")]"
        $ expectFailure
        $ parseTrusted $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern trustedSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[trusted{illegal}()]"
        $ expectFailure
        $ parseTrusted $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = trustedId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
