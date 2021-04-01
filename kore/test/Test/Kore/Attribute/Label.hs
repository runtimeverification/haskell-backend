{-# LANGUAGE Strict #-}

module Test.Kore.Attribute.Label (
    test_Label,
    test_Attributes,
    test_duplicate,
    test_arguments,
    test_parameters,
) where

import Kore.Attribute.Label
import Kore.Syntax.Pattern
import Prelude.Kore
import Test.Kore.Attribute.Parser
import Test.Tasty
import Test.Tasty.HUnit

parseLabel :: Attributes -> Parser Label
parseLabel = parseAttributes

attribute :: AttributePattern
attribute = labelAttribute "text"

test_Label :: TestTree
test_Label =
    testCase "[label{}(\"text\")] :: Label" $
        expectSuccess Label{unLabel = Just "text"} $
            parseLabel $ Attributes [attribute]

test_Attributes :: TestTree
test_Attributes =
    testCase "[label{}(\"text\")] :: Attributes" $
        expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [attribute]

test_duplicate :: TestTree
test_duplicate =
    testCase "[label{}(\"text\"), label{}(\"text\")]" $
        expectFailure $
            parseLabel $ Attributes [attribute, attribute]

test_arguments :: TestTree
test_arguments =
    testCase "[label{}()]" $
        expectFailure $
            parseLabel $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias = labelSymbol
                , applicationChildren = []
                }

test_parameters :: TestTree
test_parameters =
    testCase "[label{illegal}(\"text\")]" $
        expectFailure $
            parseLabel $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern
            SymbolOrAlias
                { symbolOrAliasConstructor = labelId
                , symbolOrAliasParams =
                    [SortVariableSort (SortVariable "illegal")]
                }
            [attributeString "text"]
