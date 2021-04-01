{-# LANGUAGE Strict #-}
module Test.Kore.Attribute.Idem (
    test_idem,
    test_Attributes,
    test_duplicate,
    test_arguments,
    test_parameters,
) where

import Kore.Attribute.Idem
import Kore.Syntax.Pattern
import Prelude.Kore
import Test.Kore.Attribute.Parser
import Test.Tasty
import Test.Tasty.HUnit

parseIdem :: Attributes -> Parser Idem
parseIdem = parseAttributes

test_idem :: TestTree
test_idem =
    testCase "[idem{}()] :: Idem" $
        expectSuccess Idem{isIdem = True} $
            parseIdem $ Attributes [idemAttribute]

test_Attributes :: TestTree
test_Attributes =
    testCase "[idem{}()] :: Attributes" $
        expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [idemAttribute]

test_duplicate :: TestTree
test_duplicate =
    testCase "[idem{}(), idem{}()]" $
        expectFailure $
            parseIdem $ Attributes [idemAttribute, idemAttribute]

test_arguments :: TestTree
test_arguments =
    testCase "[idem{}(\"illegal\")]" $
        expectFailure $
            parseIdem $ Attributes [illegalAttribute]
  where
    illegalAttribute = attributePattern idemSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[idem{illegal}()]" $
        expectFailure $
            parseIdem $ Attributes [illegalAttribute]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = idemId
                        , symbolOrAliasParams =
                            [SortVariableSort (SortVariable "illegal")]
                        }
                , applicationChildren = []
                }
