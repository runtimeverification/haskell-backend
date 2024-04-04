module Test.Kore.Attribute.Axiom.Unit (
    test_unit,
    test_Attributes,
    test_duplicate,
    test_arguments,
    test_parameters,
) where

import Kore.Attribute.Axiom.Unit
import Kore.Syntax.Pattern
import Prelude.Kore
import Test.Kore.Attribute.Parser
import Test.Tasty
import Test.Tasty.HUnit

parseUnit :: Attributes -> Parser Unit
parseUnit = parseAttributes

test_unit :: TestTree
test_unit =
    testCase "[unit{}()] :: Unit" $
        expectSuccess Unit{isUnit = True} $
            parseUnit $
                Attributes [unitAttribute]

test_Attributes :: TestTree
test_Attributes =
    testCase "[unit{}()] :: Attributes" $
        expectSuccess attrs $
            parseAttributes attrs
  where
    attrs = Attributes [unitAttribute]

test_duplicate :: TestTree
test_duplicate =
    testCase "[unit{}(), unit{}()]" $
        expectFailure $
            parseUnit $
                Attributes [unitAttribute, unitAttribute]

test_arguments :: TestTree
test_arguments =
    testCase "[unit{}(\"illegal\")]" $
        expectFailure $
            parseUnit $
                Attributes [illegalAttribute]
  where
    illegalAttribute = attributePattern unitSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[unit{illegal}()]" $
        expectFailure $
            parseUnit $
                Attributes [illegalAttribute]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = unitId
                        , symbolOrAliasParams =
                            [SortVariableSort (SortVariable "illegal")]
                        }
                , applicationChildren = []
                }
