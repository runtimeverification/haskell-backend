module Test.Kore.Attribute.Simplification
    ( test_simplification
    , test_Attributes
    , test_duplicate
    , test_arguments
    , test_parameters
    ) where

import Prelude.Kore

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Simplification
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseSimplification :: Attributes -> Parser Simplification
parseSimplification = parseAttributes

test_simplification :: TestTree
test_simplification =
    testCase "[simplification{}()] :: Simplification"
        $ expectSuccess (IsSimplification Nothing)
        $ parseSimplification $ Attributes [ simplificationAttribute Nothing ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[simplification{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ simplificationAttribute Nothing ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[simplification{}(), simplification{}()]"
        $ expectFailure
        $ parseSimplification
        $ Attributes [ simplificationAttribute Nothing, simplificationAttribute Nothing ]

test_arguments :: TestTree
test_arguments =
    testCase "[simplification{}(\"illegal\")]"
        $ expectFailure
        $ parseSimplification $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern simplificationSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[simplification{illegal}()]"
        $ expectFailure
        $ parseSimplification $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = simplificationId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
