module Test.Kore.Attribute.Priority where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Priority
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parsePriority :: Attributes -> Parser Priority
parsePriority = parseAttributes

test_priority :: TestTree
test_priority =
    testCase "[priority{}(\"123\")] :: Priority"
        $ expectSuccess Priority { getPriority = Just 123 }
        $ parsePriority
        $ Attributes [ priorityAttribute "123" ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[priority{}(\"123\")] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ priorityAttribute "123"]

test_duplicate :: TestTree
test_duplicate =
    testCase "[priority{}(\"123\")], priority{}(\"123\")]"
        $ expectFailure
        $ parsePriority $ Attributes [ attr, attr]
  where
    attr = priorityAttribute "123"

test_zeroArguments :: TestTree
test_zeroArguments =
    testCase "[priority{}()]"
        $ expectFailure
        $ parsePriority $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias = prioritySymbol
                , applicationChildren = []
                }

test_twoArguments :: TestTree
test_twoArguments =
    testCase "[priority{}(\"illegal\", \"illegal\")]"
        $ expectFailure
        $ parsePriority $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern prioritySymbol
            [attributeString "illegal", attributeString "illegal"]

test_negative :: TestTree
test_negative =
    testCase "[priority{}(\"-32\")]"
        $ expectSuccess Priority { getPriority = Just (-32) }
        $ parsePriority
        $ Attributes [ priorityAttribute "-32"]

test_string :: TestTree
test_string =
    testCase "[priority{}(\"abc\")]"
        $ expectFailure
        $ parsePriority $ Attributes [ attr ]
  where
    attr = priorityAttribute "abc"


test_space :: TestTree
test_space =
    testCase "[priority{}(\" \")]"
        $ expectFailure
        $ parsePriority $ Attributes [ attr ]
  where
    attr = priorityAttribute " "
