module Test.Kore.Attribute.Symbol.Klabel (test_Klabel) where

import Prelude.Kore

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Symbol.Klabel
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseKlabel :: Attributes -> Parser Klabel
parseKlabel = parseAttributes

test_Klabel :: [TestTree]
test_Klabel =
    [ testCase "[klabel{}(\"string\")] :: Klabel" $
        expectSuccess Klabel{getKlabel = Just "string"}
            . parseKlabel
            $ Attributes [klabelAttribute "string"]
    , testCase "[klabel{}(\"string\")] :: Attributes" $ do
        let attrs = Attributes [klabelAttribute "string"]
        expectSuccess attrs $ parseAttributes attrs
    , testCase "[klabel{}(\"string\"), klabel{}(\"string\")]" $ do
        let attr = klabelAttribute "string"
        expectFailure . parseKlabel $ Attributes [attr, attr]
    , testCase "[klabel{}()]" $ do
        let illegalAttribute =
                (asAttributePattern . ApplicationF)
                    Application
                        { applicationSymbolOrAlias = klabelSymbol
                        , applicationChildren = []
                        }
        expectFailure . parseKlabel $ Attributes [illegalAttribute]
    , testCase "[klabel{}(\"illegal\", \"illegal\")]" $ do
        let illegalAttribute =
                attributePattern
                    klabelSymbol
                    [attributeString "illegal", attributeString "illegal"]
        expectFailure . parseKlabel $ Attributes [illegalAttribute]
    , testCase "[klabel{illegal}(\"string\")]" $ do
        let illegalAttribute =
                attributePattern
                    SymbolOrAlias
                        { symbolOrAliasConstructor = klabelId
                        , symbolOrAliasParams =
                            [SortVariableSort (SortVariable "illegal")]
                        }
                    [attributeString "string"]
        expectFailure . parseKlabel $ Attributes [illegalAttribute]
    ]
