module Test.Kore.Attribute.Symbol.Memo where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Symbol.Memo
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseMemo :: Attributes -> Parser Memo
parseMemo = parseAttributes

test_memo :: TestTree
test_memo =
    testCase "[memo{}()] :: Memo"
        $ expectSuccess Memo { isMemo = True }
        $ parseMemo $ Attributes [ memoAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[memo{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ memoAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[memo{}(), memo{}()]"
        $ expectFailure $ parseMemo
        $ Attributes [ memoAttribute, memoAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[memo{}(\"illegal\")]"
        $ expectFailure
        $ parseMemo $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern memoSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[memo{illegal}()]"
        $ expectFailure
        $ parseMemo $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = memoId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
