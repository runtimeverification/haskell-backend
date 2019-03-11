module Test.Kore.Attribute.Sort.Unit where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.AST.Kore
import Kore.AST.Sentence
import Kore.Attribute.Sort.Unit

import Test.Kore.Attribute.Parser

parseUnit :: Attributes -> Parser Unit
parseUnit = parseAttributes

test_Unit :: TestTree
test_Unit =
    testCase "[unit{}(unit{}())] :: Unit"
    $ expectSuccess Unit { getUnit = Just unitSymbol }
    $ parseUnit $ Attributes [ unitAttribute unitSymbol ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[unit{}(unit{}())] :: Attributes"
    $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ unitAttribute unitSymbol ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[unit{}(_), unit{}(_)]"
    $ expectFailure
    $ parseUnit
    $ Attributes
        [ unitAttribute unitSymbol
        , unitAttribute unitSymbol
        ]

test_arity :: TestTree
test_arity =
    testCase "[unit{}(unit{}(), unit{}())]"
    $ expectFailure
    $ parseUnit $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asCommonKorePattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias = unitSymbol
                , applicationChildren =
                    [ (asCommonKorePattern . ApplicationPattern)
                        Application
                            { applicationSymbolOrAlias = unitSymbol
                            , applicationChildren = []
                            }
                    , (asCommonKorePattern . ApplicationPattern)
                        Application
                            { applicationSymbolOrAlias = unitSymbol
                            , applicationChildren = []
                            }
                    ]
                }

test_arguments :: TestTree
test_arguments =
    testCase "[unit{}(\"illegal\")]"
    $ expectFailure
    $ parseUnit $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asCommonKorePattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias = unitSymbol
                , applicationChildren =
                    [ (asCommonKorePattern . StringLiteralPattern)
                        (StringLiteral "illegal")
                    ]
                }

test_parameters :: TestTree
test_parameters =
    testCase "[unit{illegal}()]"
    $ expectFailure
    $ parseUnit $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asCommonKorePattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = unitId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
