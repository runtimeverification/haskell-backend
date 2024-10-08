module Test.Kore.Attribute.Symbol.SymbolKywd (
    test_symbolKywd,
    test_Attributes,
    test_duplicate,
    test_argument,
    test_2arguments,
    test_parameters,
) where

import Kore.Attribute.Symbol.SymbolKywd
import Kore.Syntax.Pattern
import Prelude.Kore
import Test.Kore.Attribute.Parser
import Test.Tasty
import Test.Tasty.HUnit

parseSymbolKywd :: Attributes -> Parser SymbolKywd
parseSymbolKywd = parseAttributes

test_symbolKywd :: TestTree
test_symbolKywd =
    testCase "[symbolKywd{}()] :: SymbolKywd" $
        expectSuccess SymbolKywd{getSymbolKywd = Just ""} $
            parseSymbolKywd $
                Attributes [symbolKywdAttribute ""]

test_Attributes :: TestTree
test_Attributes =
    testCase "[symbolKywd{}()] :: Attributes" $
        expectSuccess attrs $
            parseAttributes attrs
  where
    attrs = Attributes [symbolKywdAttribute ""]

test_duplicate :: TestTree
test_duplicate =
    testCase "[symbolKywd{}(), symbolKywd{}()]" $
        expectFailure $
            parseSymbolKywd $
                Attributes [symbolKywdAttribute "", symbolKywdAttribute ""]

test_argument :: TestTree
test_argument =
    testCase "[symbolKywd{}(\"legal\")]" $
        expectSuccess SymbolKywd{getSymbolKywd = Just "legal"} $
            parseSymbolKywd $
                Attributes [legalAttribute]
  where
    legalAttribute =
        attributePattern symbolKywdSymbol [attributeString "legal"]

test_2arguments :: TestTree
test_2arguments =
    testCase "[symbolKywd{}(\"not\", \"allowed\")]" $
        expectFailure $
            parseSymbolKywd $
                Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern symbolKywdSymbol [attributeString "not", attributeString "allowed"]

test_parameters :: TestTree
test_parameters =
    testCase "[symbolKywd{illegal}()]" $
        expectFailure $
            parseSymbolKywd $
                Attributes [illegalAttribute]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = symbolKywdId
                        , symbolOrAliasParams =
                            [SortVariableSort (SortVariable "illegal")]
                        }
                , applicationChildren = []
                }
