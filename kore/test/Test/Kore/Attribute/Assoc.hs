{-# LANGUAGE Strict #-}

module Test.Kore.Attribute.Assoc (
    test_assoc,
    test_Attributes,
    test_duplicate,
    test_arguments,
    test_parameters,
) where

import Kore.Attribute.Assoc
import Kore.Syntax.Pattern
import Prelude.Kore
import Test.Kore.Attribute.Parser
import Test.Tasty
import Test.Tasty.HUnit

parseAssoc :: Attributes -> Parser Assoc
parseAssoc = parseAttributes

test_assoc :: TestTree
test_assoc =
    testCase "[assoc{}()] :: Assoc" $
        expectSuccess Assoc{isAssoc = True} $
            parseAssoc $ Attributes [assocAttribute]

test_Attributes :: TestTree
test_Attributes =
    testCase "[assoc{}()] :: Attributes" $
        expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [assocAttribute]

test_duplicate :: TestTree
test_duplicate =
    testCase "[assoc{}(), assoc{}()]" $
        expectFailure $
            parseAssoc $ Attributes [assocAttribute, assocAttribute]

test_arguments :: TestTree
test_arguments =
    testCase "[assoc{}(\"illegal\")]" $
        expectFailure $
            parseAssoc $ Attributes [illegalAttribute]
  where
    illegalAttribute = attributePattern assocSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[assoc{illegal}()]" $
        expectFailure $
            parseAssoc $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = assocId
                        , symbolOrAliasParams =
                            [SortVariableSort (SortVariable "illegal")]
                        }
                , applicationChildren = []
                }
