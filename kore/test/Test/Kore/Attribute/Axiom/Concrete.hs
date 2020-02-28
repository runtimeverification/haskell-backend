module Test.Kore.Attribute.Axiom.Concrete
    ( test_concrete
    , test_Attributes
    , test_parameters
    , test_duplicate
    , test_arguments
    ) where

import Prelude.Kore

import Test.Tasty
import Test.Tasty.HUnit

import qualified Data.Default as Default
import qualified Data.Foldable as Foldable

import Kore.Attribute.Axiom.Concrete
import Kore.Attribute.Pattern.FreeVariables as FreeVariables
import Kore.Syntax.Variable
    ( Variable (..)
    )

import Test.Kore.Attribute.Parser

parseConcrete :: Attributes -> Parser (Concrete Variable)
parseConcrete (Attributes attrs) =
    Foldable.foldlM
        (\c a -> parseConcreteAttribute a Default.def c)
        Default.def
        attrs

test_concrete :: TestTree
test_concrete =
    testCase "[concrete{}()] :: Concrete"
        $ expectSuccess Concrete { freeVariables = FreeVariables.freeVariables concreteAttribute }
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
