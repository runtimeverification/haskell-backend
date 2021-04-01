{-# LANGUAGE Strict #-}
module Test.Kore.Attribute.Owise (
    test_owise,
    test_attributes,
    test_parameters,
    test_duplicate,
    test_arguments,
) where

import Kore.Attribute.Owise
import Prelude.Kore
import Test.Kore.Attribute.Parser
import Test.Tasty
import Test.Tasty.HUnit

parseOwise :: Attributes -> Parser Owise
parseOwise = parseAttributes

test_owise :: TestTree
test_owise =
    testCase "[owise{}()] :: Owise" $
        expectSuccess Owise{isOwise = True} $
            parseOwise $ Attributes [owiseAttribute]

test_attributes :: TestTree
test_attributes =
    testCase "[owise{}()] :: Attributes" $
        expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [owiseAttribute]

test_duplicate :: TestTree
test_duplicate =
    testCase "[owise{}(), owise{}()]" $
        expectFailure $
            parseOwise $ Attributes [owiseAttribute, owiseAttribute]

test_arguments :: TestTree
test_arguments =
    testCase "[owise{}(\"illegal\")]" $
        expectFailure $
            parseOwise $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern owiseSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[owise{illegal}()]" $
        expectFailure $
            parseOwise $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern_
            SymbolOrAlias
                { symbolOrAliasConstructor = owiseId
                , symbolOrAliasParams =
                    [SortVariableSort (SortVariable "illegal")]
                }
