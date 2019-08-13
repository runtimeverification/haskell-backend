module Test.Kore.Attribute.Constructor where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Constructor
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseConstructor :: Attributes -> Parser Constructor
parseConstructor = parseAttributes

test_constructor :: TestTree
test_constructor =
    testCase "[constructor{}()] :: Constructor"
        $ expectSuccess Constructor { isConstructor = True }
        $ parseConstructor $ Attributes [ constructorAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[constructor{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ constructorAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[constructor{}(), constructor{}()]"
        $ expectFailure $ parseConstructor
        $ Attributes [ constructorAttribute, constructorAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[constructor{}(\"illegal\")]"
    $ expectFailure
    $ parseConstructor $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern constructorSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[constructor{illegal}()]"
        $ expectFailure
        $ parseConstructor $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = constructorId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
