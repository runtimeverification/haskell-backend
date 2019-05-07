module Test.Kore.Attribute.Axiom.Concrete where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Attribute.Axiom.Concrete

import Test.Kore.Attribute.Parser

parseConcrete :: Attributes -> Parser Concrete
parseConcrete = parseAttributes

test_concrete :: TestTree
test_concrete =
    testCase "[concrete{}()] :: Concrete"
        $ expectSuccess Concrete { isConcrete = True }
        $ parseConcrete $ Attributes [ concreteAttribute ]

test_Attributes :: TestTree
test_Attributes =
    testCase "[concrete{}()] :: Attributes"
        $ expectSuccess attrs $ parseAttributes attrs
  where
    attrs = Attributes [ concreteAttribute ]

test_duplicate :: TestTree
test_duplicate =
    testCase "[concrete{}(), concrete{}()]"
        $ expectFailure
        $ parseConcrete $ Attributes [ concreteAttribute, concreteAttribute ]

test_arguments :: TestTree
test_arguments =
    testCase "[concrete{}(\"illegal\")]"
        $ expectFailure
        $ parseConcrete $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern concreteSymbol [attributeString "illegal"]

test_parameters :: TestTree
test_parameters =
    testCase "[concrete{illegal}()]"
        $ expectFailure
        $ parseConcrete $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern_
            SymbolOrAlias
                { symbolOrAliasConstructor = concreteId
                , symbolOrAliasParams =
                    [ SortVariableSort (SortVariable "illegal") ]
                }
