module Test.Kore.Attribute.HeatCool where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.HeatCool
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseHeatCool :: Attributes -> Parser HeatCool
parseHeatCool = parseAttributes

test_heat :: TestTree
test_heat =
    testCase "[heat{}()] :: Heat"
        $ expectSuccess Heat
        $ parseHeatCool $ Attributes [ heatAttribute ]

test_heat_Attributes :: TestTree
test_heat_Attributes =
    testCase "[heat{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ heatAttribute ]

test_heat_duplicate :: TestTree
test_heat_duplicate =
    testCase "[heat{}(), heat{}()]"
        $ expectFailure
        $ parseHeatCool $ Attributes [ heatAttribute, heatAttribute ]

test_heat_arguments :: TestTree
test_heat_arguments =
    testCase "[heat{}(\"illegal\")]"
        $ expectFailure
        $ parseHeatCool $ Attributes [ illegalAttribute ]
  where
    illegalAttribute = attributePattern heatSymbol [attributeString "illegal"]

test_heat_parameters :: TestTree
test_heat_parameters =
    testCase "[heat{illegal}()]"
        $ expectFailure
        $ parseHeatCool $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = heatId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }

test_cool :: TestTree
test_cool =
    testCase "[cool{}()] :: HeatCool"
        $ expectSuccess Cool
        $ parseHeatCool $ Attributes [ coolAttribute ]

test_cool_Attributes :: TestTree
test_cool_Attributes =
    testCase "[cool{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ coolAttribute ]

test_cool_duplicate :: TestTree
test_cool_duplicate =
    testCase "[cool{}(), cool{}()]"
        $ expectFailure
        $ parseHeatCool $ Attributes [ coolAttribute, coolAttribute ]

test_cool_arguments :: TestTree
test_cool_arguments =
    testCase "[cool{}(\"illegal\")]"
        $ expectFailure
        $ parseHeatCool $ Attributes [ illegalAttribute ]
  where
    illegalAttribute = attributePattern coolSymbol [attributeString "illegal"]

test_cool_parameters :: TestTree
test_cool_parameters =
    testCase "[cool{illegal}()]"
        $ expectFailure
        $ parseHeatCool $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = coolId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }

test_conflict :: TestTree
test_conflict =
    testGroup "conflicting attributes"
        [ testCase "[heat{}(), cool{}()] :: HeatCool"
            $ expectFailure
            $ parseHeatCool $ Attributes [ heatAttribute, coolAttribute ]
        , testCase "[cool{}(), heat{}()] :: HeatCool"
            $ expectFailure
            $ parseHeatCool $ Attributes [ coolAttribute, heatAttribute ]
        ]
