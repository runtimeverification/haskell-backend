module Test.Kore.Attribute.Sort.Unit where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Sort.Unit
import Kore.Syntax.Definition
import Kore.Syntax.Pattern

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
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias = unitSymbol
                , applicationChildren =
                    [ (asAttributePattern . ApplicationF)
                        Application
                            { applicationSymbolOrAlias = unitSymbol
                            , applicationChildren = []
                            }
                    , (asAttributePattern . ApplicationF)
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
    illegalAttribute = attributePattern unitSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[unit{illegal}()]"
    $ expectFailure
    $ parseUnit $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = unitId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
