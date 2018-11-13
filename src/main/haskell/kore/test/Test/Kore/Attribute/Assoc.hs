module Test.Kore.Attribute.Assoc where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.AST.Common
import Kore.AST.Kore
import Kore.Attribute.Assoc

import Test.Kore.Attribute.Parser

parseAssoc :: Attributes -> Parser Assoc
parseAssoc = parseAttributes

test_assoc :: TestTree
test_assoc =
    testCase "[assoc{}()] :: Assoc"
        $ expectSuccess Assoc { isAssoc = True }
        $ parseAssoc $ Attributes [ assocAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[assoc{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ assocAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[assoc{}(), assoc{}()]"
        $ expectFailure
        $ parseAssoc $ Attributes [ assocAttribute, assocAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[assoc{}(\"illegal\")]"
        $ expectFailure
        $ parseAssoc $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (KoreObjectPattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias = assocSymbol
                , applicationChildren =
                    [ (KoreMetaPattern . StringLiteralPattern)
                        (StringLiteral "illegal")
                    ]
                }

test_parameters :: TestTree
test_parameters =
    testCase "[assoc{illegal}()]"
        $ expectFailure
        $ parseAssoc $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (KoreObjectPattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = assocId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
