module Test.Kore.Attribute.NonExecutable (
    test_nonExecutable,
    test_Attributes,
    test_duplicate,
    test_parameters,
    test_arguments,
) where

import Kore.Attribute.Axiom.NonExecutable
import Kore.Syntax.Pattern
import Prelude.Kore
import Test.Kore.Attribute.Parser
import Test.Tasty
import Test.Tasty.HUnit

parseNonExecutable :: Attributes -> Parser NonExecutable
parseNonExecutable = parseAttributes

test_nonExecutable :: TestTree
test_nonExecutable =
    testCase "[non-executable{}()] :: NonExecutable" $
        expectSuccess NonExecutable{isNonExecutable = True} $
            parseNonExecutable $ Attributes [nonExecutableAttribute]

test_Attributes :: TestTree
test_Attributes =
    testCase "[non-executable{}()] :: Attributes" $
        expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [nonExecutableAttribute]

test_duplicate :: TestTree
test_duplicate =
    testCase "[non-executable{}(), non-executable{}()]" $
        expectFailure $
            parseNonExecutable $
                Attributes [nonExecutableAttribute, nonExecutableAttribute]

test_arguments :: TestTree
test_arguments =
    testCase "[non-executable{}(\"illegal\")]" $
        expectFailure $
            parseNonExecutable $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern nonExecutableSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[non-executable{illegal}()]" $
        expectFailure $
            parseNonExecutable $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = nonExecutableId
                        , symbolOrAliasParams =
                            [SortVariableSort (SortVariable "illegal")]
                        }
                , applicationChildren = []
                }
