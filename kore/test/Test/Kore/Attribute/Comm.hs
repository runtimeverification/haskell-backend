module Test.Kore.Attribute.Comm where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Comm
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseComm :: Attributes -> Parser Comm
parseComm = parseAttributes

test_comm :: TestTree
test_comm =
    testCase "[comm{}()] :: Comm"
        $ expectSuccess Comm { isComm = True }
        $ parseComm $ Attributes [ commAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[comm{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ commAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[comm{}(), comm{}()]"
        $ expectFailure
        $ parseComm $ Attributes [ commAttribute, commAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[comm{}(\"illegal\")]"
        $ expectFailure
        $ parseComm $ Attributes [ illegalAttribute ]
  where
    illegalAttribute = attributePattern commSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[comm{illegal}()]"
        $ expectFailure
        $ parseComm $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = commId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
