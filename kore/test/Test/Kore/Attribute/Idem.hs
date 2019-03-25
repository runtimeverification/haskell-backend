module Test.Kore.Attribute.Idem where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.AST.Kore
import Kore.Attribute.Idem

import Test.Kore.Attribute.Parser

parseIdem :: Attributes -> Parser Idem
parseIdem = parseAttributes

test_idem :: TestTree
test_idem =
    testCase "[idem{}()] :: Idem"
        $ expectSuccess Idem { isIdem = True }
        $ parseIdem $ Attributes [ idemAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[idem{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ idemAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[idem{}(), idem{}()]"
        $ expectFailure
        $ parseIdem $ Attributes [ idemAttribute, idemAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[idem{}(\"illegal\")]"
        $ expectFailure
        $ parseIdem $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asCommonKorePattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias = idemSymbol
                , applicationChildren =
                    [ (asCommonKorePattern . StringLiteralPattern)
                        (StringLiteral "illegal")
                    ]
                }

test_parameters :: TestTree
test_parameters =
    testCase "[idem{illegal}()]"
        $ expectFailure
        $ parseIdem $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asCommonKorePattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = idemId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
