module Test.Kore.Attribute.Overload where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.AST.Kore
import Kore.Attribute.Overload

import Test.Kore
import Test.Kore.Attribute.Parser

parseOverload :: Attributes -> Parser Overload
parseOverload = parseAttributes

superSymbol :: SymbolOrAlias Object
superSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId "superSymbol"
        , symbolOrAliasParams = []
        }

subSymbol :: SymbolOrAlias Object
subSymbol =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId "subSymbol"
        , symbolOrAliasParams = []
        }

test_Overload :: TestTree
test_Overload =
    testCase "[overload{}(superSymbol{}(), subSymbol{}())] :: Overload"
    $ expectSuccess Overload { overload = Just (superSymbol, subSymbol) }
    $ parseOverload $ Attributes [ overloadAttribute superSymbol subSymbol ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[overload{}(superSymbol{}(), subSymbol{}())] :: Attributes"
    $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ overloadAttribute superSymbol subSymbol ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[overload{}(_, _), overload{}(_, _)]"
    $ expectFailure
    $ parseOverload
    $ Attributes
        [ overloadAttribute superSymbol subSymbol
        , overloadAttribute superSymbol subSymbol
        ]

test_arguments :: TestTree
test_arguments =
    testCase "[overload{}(\"illegal\")]"
    $ expectFailure
    $ parseOverload $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asCommonKorePattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias = overloadSymbol
                , applicationChildren =
                    [ (asCommonKorePattern . StringLiteralPattern)
                        (StringLiteral "illegal")
                    ]
                }

test_parameters :: TestTree
test_parameters =
    testCase "[overload{illegal}()]"
    $ expectFailure
    $ parseOverload $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asCommonKorePattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = overloadId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
