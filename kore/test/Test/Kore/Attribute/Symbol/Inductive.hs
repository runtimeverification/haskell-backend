module Test.Kore.Attribute.Inductive where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Set as Set

import Kore.Attribute.Inductive
import Kore.Syntax.Pattern

import Test.Kore.Attribute.Parser

parseInductive :: Attributes -> Parser Inductive
parseInductive = parseAttributes

test_inductive :: [TestTree]
test_inductive =
    [ testCase "[inductive{}(1)] :: Inductive"
        $ expectSuccess Inductive { inductiveArguments = Set.singleton 1 }
        $ parseInductive $ Attributes [ inductiveAttribute 1 ]
    , testCase "[inductive{}(1)] :: Attributes"
        $ expectSuccess Attributes [ inductiveAttribute 1 ]
        $ parseAttributes Attributes [ inductiveAttribute 1 ]
    , testCase "[inductive{}(1), inductive{}(1)]"
        $ expectSuccess Inductive { inductiveArguments = Set.singleton 1 }
        $ parseInductive
        $ Attributes [ inductiveAttribute 1, inductiveAttribute 1 ]
    , testCase "[inductive{}(1), inductive{}(2)]"
        $ expectSuccess Inductive { inductiveArguments = Set.fromList [1, 2] }
        $ parseInductive
        $ Attributes [ inductiveAttribute 1, inductiveAttribute 2 ]
    ]

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
