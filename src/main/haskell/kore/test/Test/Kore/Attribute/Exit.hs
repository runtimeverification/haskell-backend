module Test.Kore.Attribute.Exit where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.AST.Kore
import Kore.Attribute.Exit

import Test.Kore.Attribute.Parser

parseExit :: Attributes -> Parser Exit
parseExit = parseAttributes

test_exit :: TestTree
test_exit =
    testCase "[exit{}()] :: Exit"
        $ expectSuccess Exit { isExit = True }
        $ parseExit $ Attributes [ exitAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[exit{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ exitAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[exit{}(), exit{}()]"
        $ expectFailure $ parseExit
        $ Attributes [ exitAttribute, exitAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[exit{}(\"illegal\")]"
        $ expectFailure
        $ parseExit $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asCommonKorePattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias = exitSymbol
                , applicationChildren =
                    [ (asCommonKorePattern . StringLiteralPattern)
                        (StringLiteral "illegal")
                    ]
                }

test_parameters :: TestTree
test_parameters =
    testCase "[exit{illegal}()]"
        $ expectFailure
        $ parseExit $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asCommonKorePattern . ApplicationPattern)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = exitId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
