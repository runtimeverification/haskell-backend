{-# LANGUAGE Strict #-}

module Test.Kore.Attribute.Functional (
    test_functional,
    test_Attributes,
    test_duplicate,
    test_parameters,
    test_arguments,
) where

import Kore.Attribute.Functional
import Kore.Syntax.Pattern
import Prelude.Kore
import Test.Kore.Attribute.Parser
import Test.Tasty
import Test.Tasty.HUnit

parseFunctional :: Attributes -> Parser Functional
parseFunctional = parseAttributes

test_functional :: TestTree
test_functional =
    testCase "[functional{}()] :: Functional" $
        expectSuccess Functional{isDeclaredFunctional = True} $
            parseFunctional $ Attributes [functionalAttribute]

test_Attributes :: TestTree
test_Attributes =
    testCase "[functional{}()] :: Attributes" $
        expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [functionalAttribute]

test_duplicate :: TestTree
test_duplicate =
    testCase "[functional{}(), functional{}()]" $
        expectFailure $
            parseFunctional $
                Attributes [functionalAttribute, functionalAttribute]

test_arguments :: TestTree
test_arguments =
    testCase "[functional{}(\"illegal\")]" $
        expectFailure $
            parseFunctional $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        attributePattern functionalSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[functional{illegal}()]" $
        expectFailure $
            parseFunctional $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = functionalId
                        , symbolOrAliasParams =
                            [SortVariableSort (SortVariable "illegal")]
                        }
                , applicationChildren = []
                }
