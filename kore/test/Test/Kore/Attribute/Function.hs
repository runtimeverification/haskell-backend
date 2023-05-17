module Test.Kore.Attribute.Function (
    test_function,
    test_Attributes,
    test_duplicate,
    test_arguments,
    test_parameters,
) where

import Kore.Attribute.Function
import Kore.Syntax.Pattern
import Prelude.Kore
import Test.Kore.Attribute.Parser
import Test.Tasty
import Test.Tasty.HUnit

parseFunction :: Attributes -> Parser Function
parseFunction = parseAttributes

test_function :: TestTree
test_function =
    testCase "[function{}()] :: Function" $
        expectSuccess Function{isDeclaredFunction = True} $
            parseFunction $
                Attributes [functionAttribute]

test_Attributes :: TestTree
test_Attributes =
    testCase "[function{}()] :: Attributes" $
        expectSuccess attrs $
            parseAttributes attrs
  where
    attrs = Attributes [functionAttribute]

test_duplicate :: TestTree
test_duplicate =
    testCase "[function{}(), function{}()]" $
        expectFailure $
            parseFunction $
                Attributes [functionAttribute, functionAttribute]

test_arguments :: TestTree
test_arguments =
    testCase "[function{}(\"illegal\")]" $
        expectFailure $
            parseFunction $
                Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern functionSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[function{illegal}()]" $
        expectFailure $
            parseFunction $
                Attributes [illegalAttribute]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = functionId
                        , symbolOrAliasParams =
                            [SortVariableSort (SortVariable "illegal")]
                        }
                , applicationChildren = []
                }
