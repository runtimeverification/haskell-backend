module Test.Kore.Attribute.SortInjection where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.SortInjection
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseSortInjection :: Attributes -> Parser SortInjection
parseSortInjection = parseAttributes

test_sortInjection :: TestTree
test_sortInjection =
    testCase "[sortInjection{}()] :: SortInjection"
        $ expectSuccess SortInjection { isSortInjection = True }
        $ parseSortInjection $ Attributes [ sortInjectionAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[sortInjection{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ sortInjectionAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[sortInjection{}(), sortInjection{}()]"
        $ expectFailure $ parseSortInjection
        $ Attributes [ sortInjectionAttribute, sortInjectionAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[sortInjection{}(\"illegal\")]"
        $ expectFailure
        $ parseSortInjection $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern sortInjectionSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[sortInjection{illegal}()]"
        $ expectFailure
        $ parseSortInjection $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = sortInjectionId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
