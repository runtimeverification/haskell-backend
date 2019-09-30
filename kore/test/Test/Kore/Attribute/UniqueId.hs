module Test.Kore.Attribute.UniqueId where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.UniqueId
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseUniqueId :: Attributes -> Parser UniqueId
parseUniqueId = parseAttributes

attribute :: AttributePattern
attribute = uniqueIdAttribute "text"

test_UniqueId :: TestTree
test_UniqueId =
    testCase "[UNIQUE'Unds'ID{}(\"text\")] :: UniqueId"
    $ expectSuccess UniqueId { getUniqueId = Just "text" }
    $ parseUniqueId $ Attributes [ attribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[UNIQUE'Unds'ID{}(\"text\")] :: Attributes"
    $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ attribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[UNIQUE'Unds'ID{}(\"text\"), uniqueId{}(\"text\")]"
    $ expectFailure
    $ parseUniqueId $ Attributes [ attribute, attribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[UNIQUE'Unds'ID{}()]"
    $ expectFailure
    $ parseUniqueId $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias = uniqueIdSymbol
                , applicationChildren = []
                }

test_parameters :: TestTree
test_parameters =
    testCase "[UNIQUE'Unds'ID{illegal}(\"text\")]"
    $ expectFailure
    $ parseUniqueId $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern
            SymbolOrAlias
                { symbolOrAliasConstructor = uniqueIdId
                , symbolOrAliasParams =
                    [ SortVariableSort (SortVariable "illegal") ]
                }
            [attributeString "text"]
