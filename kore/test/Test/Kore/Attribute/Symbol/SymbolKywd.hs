module Test.Kore.Attribute.Symbol.SymbolKywd (
    test_symbolKywd,
    -- test_Attributes,
    -- test_duplicate,
    -- test_arguments,
    -- test_parameters,
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
  testGroup "symbolKyWd tests" 
    [
      testCase "[symbolKywd{}()] :: SymbolKywd" $
        expectSuccess SymbolKywd{getSymbol = Just ""} $
            parseSymbolKywd $
                Attributes [symbolKywdAttribute ""]
    , _test_Attributes
    , _test_duplicate
--    , _test_arguments
    , _test_parameters
    ]

_test_Attributes :: TestTree
_test_Attributes =
    testCase "[symbolKywd{}()] :: Attributes" $
        expectSuccess attrs $
            parseAttributes attrs
  where
    attrs = Attributes [symbolKywdAttribute ""]

_test_duplicate :: TestTree
_test_duplicate =
    testCase "[symbolKywd{}(), symbolKywd{}()]" $
        expectFailure $
            parseSymbolKywd $
                Attributes [symbolKywdAttribute "", symbolKywdAttribute ""]

_test_arguments :: TestTree
_test_arguments =
    testCase "[symbolKywd{}(\"legal\")]" $
        expectFailure $
            parseSymbolKywd $
                Attributes [legalAttribute]
  where
    legalAttribute =
        attributePattern symbolKywdSymbol [attributeString "legal"]

_test_parameters :: TestTree
_test_parameters =
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
