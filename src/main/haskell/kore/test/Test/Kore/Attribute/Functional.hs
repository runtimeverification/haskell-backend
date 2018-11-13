module Test.Kore.Attribute.Functional where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.AST.Common
import Kore.AST.Kore
import Kore.Attribute.Functional

import Test.Kore.Attribute.Parser

parseFunctional :: Attributes -> Parser Functional
parseFunctional = parseAttributes

test_functional :: TestTree
test_functional =
    testCase "[functional{}()] :: Functional"
        $ expectSuccess Functional { isDeclaredFunctional = True }
        $ parseFunctional $ Attributes [ functionalAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[functional{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ functionalAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[functional{}(), functional{}()]"
        $ expectFailure $ parseFunctional
        $ Attributes [ functionalAttribute, functionalAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[functional{}(\"illegal\")]"
        $ expectFailure
        $ parseFunctional $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (KoreObjectPattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias = functionalSymbol
                , applicationChildren =
                    [ (KoreMetaPattern . StringLiteralPattern)
                        (StringLiteral "illegal")
                    ]
                }

test_parameters :: TestTree
test_parameters =
    testCase "[functional{illegal}()]"
        $ expectFailure
        $ parseFunctional $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (KoreObjectPattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = functionalId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
