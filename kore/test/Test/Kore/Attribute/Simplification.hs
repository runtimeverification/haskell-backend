module Test.Kore.Attribute.Simplification (
    test_simplification,
    test_simplification_with_argument,
    test_simplification_with_empty_argument,
    test_Attributes,
    test_Attributes_with_argument,
    test_duplicate,
    test_arguments_wrong_type,
    test_multiple_arguments,
    test_parameters,
) where

import Kore.Attribute.Simplification
import Kore.Syntax.Pattern
import Prelude.Kore
import Test.Kore.Attribute.Parser
import Test.Tasty
import Test.Tasty.HUnit

parseSimplification :: Attributes -> Parser Simplification
parseSimplification = parseAttributes

test_simplification :: TestTree
test_simplification =
    testCase "[simplification{}()] :: Simplification" $
        expectSuccess (IsSimplification Nothing) $
            parseSimplification $ Attributes [simplificationAttribute Nothing]

test_simplification_with_argument :: TestTree
test_simplification_with_argument =
    testCase "[simplification{}(\"5\")] :: Simplification" $
        expectSuccess (IsSimplification (Just 5)) $
            parseSimplification $ Attributes [simplificationAttribute (Just 5)]

test_simplification_with_empty_argument :: TestTree
test_simplification_with_empty_argument =
    testCase "[simplification{}(\"\")]" $
        expectSuccess (IsSimplification Nothing) $
            parseSimplification $ Attributes [attr]
  where
    attr = attributePattern simplificationSymbol [attributeString ""]

test_Attributes :: TestTree
test_Attributes =
    testCase "[simplification{}()] :: Attributes" $
        expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [simplificationAttribute Nothing]

test_Attributes_with_argument :: TestTree
test_Attributes_with_argument =
    testCase "[simplification{}(\"5\")] :: Attributes" $
        expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [simplificationAttribute (Just 5)]

test_duplicate :: TestTree
test_duplicate =
    testCase "[simplification{}(), simplification{}()]" $
        expectFailure $
            parseSimplification $
                Attributes [simplificationAttribute Nothing, simplificationAttribute Nothing]

test_arguments_wrong_type :: TestTree
test_arguments_wrong_type =
    testCase "[simplification{}(\"illegal\")]" $
        expectFailure $
            parseSimplification $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern simplificationSymbol [attributeString "illegal"]

test_multiple_arguments :: TestTree
test_multiple_arguments =
    testCase "[simplification{}(\"3\", \"26\")]" $
        expectFailure $
            parseSimplification $ Attributes [illegalAttributes]
  where
    illegalAttributes =
        attributePattern
            simplificationSymbol
            [attributeInteger 3, attributeInteger 26]

test_parameters :: TestTree
test_parameters =
    testCase "[simplification{illegal}()]" $
        expectFailure $
            parseSimplification $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = simplificationId
                        , symbolOrAliasParams =
                            [SortVariableSort (SortVariable "illegal")]
                        }
                , applicationChildren = []
                }
