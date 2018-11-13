module Test.Kore.Attribute.Function where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.AST.Common
import Kore.AST.Kore
import Kore.Attribute.Function

import Test.Kore.Attribute.Parser

parseFunction :: Attributes -> Parser Function
parseFunction = parseAttributes

test_function :: TestTree
test_function =
    testCase "[function{}()] :: Function"
        $ expectSuccess Function { isDeclaredFunction = True }
        $ parseFunction $ Attributes [ functionAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[function{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ functionAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[function{}(), function{}()]"
        $ expectFailure
        $ parseFunction $ Attributes [ functionAttribute, functionAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[function{}(\"illegal\")]"
        $ expectFailure
        $ parseFunction $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (KoreObjectPattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias = functionSymbol
                , applicationChildren =
                    [ (KoreMetaPattern . StringLiteralPattern)
                        (StringLiteral "illegal")
                    ]
                }

test_parameters :: TestTree
test_parameters =
    testCase "[function{illegal}()]"
        $ expectFailure
        $ parseFunction $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (KoreObjectPattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = functionId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
