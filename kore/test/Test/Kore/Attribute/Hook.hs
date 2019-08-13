module Test.Kore.Attribute.Hook where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Hook
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseHook :: Attributes -> Parser Hook
parseHook = parseAttributes

test_hook :: TestTree
test_hook =
    testCase "[hook{}(\"BUILTIN.name\")] :: Hook"
        $ expectSuccess Hook { getHook = Just "BUILTIN.name" }
        $ parseHook $ Attributes [ hookAttribute "BUILTIN.name" ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[hook{}(\"BUILTIN.name\")] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ hookAttribute "BUILTIN.name" ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[hook{}(\"BUILTIN.name\"), hook{}(\"BUILTIN.name\")]"
        $ expectFailure
        $ parseHook $ Attributes [ attr, attr ]
  where
    attr = hookAttribute "BUILTIN.name"

test_zeroArguments :: TestTree
test_zeroArguments =
    testCase "[hook{}()]"
        $ expectFailure
        $ parseHook $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias = hookSymbol
                , applicationChildren = []
                }

test_twoArguments :: TestTree
test_twoArguments =
    testCase "[hook{}()]"
        $ expectFailure
        $ parseHook $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern hookSymbol
            [attributeString "illegal", attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[hook{illegal}(\"BUILTIN.name\")]"
        $ expectFailure
        $ parseHook $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern
            SymbolOrAlias
                { symbolOrAliasConstructor = hookId
                , symbolOrAliasParams =
                    [ SortVariableSort (SortVariable "illegal") ]
                }
            [attributeString "BUILTIN.name"]
