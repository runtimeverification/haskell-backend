module Test.Kore.Attribute.Symbol.Inductive where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Symbol.Inductive
import Kore.Syntax.Pattern
import Kore.Unparser

import Test.Kore.Attribute.Parser

parseInductive :: Attributes -> Parser Inductive
parseInductive = parseAttributes

test_Monoid :: [TestTree]
test_Monoid =
    [ testCase "right unit" $ assertEqual "" (inductive 1 <> mempty) (inductive 1)
    , testCase "left unit"  $ assertEqual "" (mempty <> inductive 1) (inductive 1)
    , testCase "idempotent" $ assertEqual "" (inductive 1 <> inductive 1) (inductive 1)
    ]

test_Attributes :: [TestTree]
test_Attributes =
    [ expectIdem [ inductiveAttribute 1 ]
    ]
  where
    expectIdem (Attributes -> attrs) =
        testCase name $ expectSuccess attrs (parseAttributes attrs)
      where
        name = show (unparse attrs <> " :: Attributes")

test_inductive :: [TestTree]
test_inductive =
    [ expecting (inductive 1)
        [ inductiveAttribute 1 ]
    , expecting (inductive 1)
        [ inductiveAttribute 1, inductiveAttribute 1 ]
    , expecting (inductive 1 <> inductive 2)
        [ inductiveAttribute 1, inductiveAttribute 2 ]
    ]
  where
    expecting expect (Attributes -> attrs) =
        testCase name $ expectSuccess expect $ parseInductive attrs
      where
        name = show (unparse attrs <> " :: Inductive")

test_arguments :: TestTree
test_arguments =
    testCase "[inductive{}(\"illegal\")]"
        $ expectFailure
        $ parseInductive $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias = inductiveSymbol
                , applicationChildren =
                    [ (asAttributePattern . StringLiteralF)
                        (StringLiteral "illegal")
                    ]
                }

test_parameters :: TestTree
test_parameters =
    testCase "[inductive{illegal}()]"
        $ expectFailure
        $ parseInductive $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        (asAttributePattern . ApplicationF)
            Application
                { applicationSymbolOrAlias =
                    SymbolOrAlias
                        { symbolOrAliasConstructor = inductiveId
                        , symbolOrAliasParams =
                            [ SortVariableSort (SortVariable "illegal") ]
                        }
                , applicationChildren = []
                }
