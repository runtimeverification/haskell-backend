module Test.Kore.Attribute.Sort.HasDomainValues where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Sort.HasDomainValues
import Kore.Syntax.Definition
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseHasDomainValues :: Attributes -> Parser HasDomainValues
parseHasDomainValues = parseAttributes

test_HasDomainValues :: TestTree
test_HasDomainValues =
    testCase "[hasDomainValues{}()] :: HasDomainValues"
    $ expectSuccess HasDomainValues { getHasDomainValues = True }
    $ parseHasDomainValues $ Attributes [ hasDomainValuesAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[hasDomainValues{}()] :: Attributes"
    $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ hasDomainValuesAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[hasDomainValues{}(_), hasDomainValues{}(_)]"
    $ expectFailure
    $ parseHasDomainValues
    $ Attributes [ hasDomainValuesAttribute, hasDomainValuesAttribute ]

test_arity :: TestTree
test_arity =
    testCase "[hasDomainValues{}(hasDomainValues{}(), hasDomainValues{}())]"
    $ expectFailure
    $ parseHasDomainValues $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias = hasDomainValuesSymbol
                , applicationChildren =
                    [ (asAttributePattern . ApplicationF)
                        Application
                            { applicationSymbolOrAlias = hasDomainValuesSymbol
                            , applicationChildren = []
                            }
                    , (asAttributePattern . ApplicationF)
                        Application
                            { applicationSymbolOrAlias = hasDomainValuesSymbol
                            , applicationChildren = []
                            }
                    ]
                }

test_arguments :: TestTree
test_arguments =
    testCase "[hasDomainValues{}(\"illegal\")]"
    $ expectFailure
    $ parseHasDomainValues $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias = hasDomainValuesSymbol
                , applicationChildren =
                    [ (asAttributePattern . StringLiteralF . Const)
                        (StringLiteral "illegal")
                    ]
                }

test_parameters :: TestTree
test_parameters =
    testCase "[hasDomainValues{illegal}()]"
    $ expectFailure
    $ parseHasDomainValues $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = hasDomainValuesId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
