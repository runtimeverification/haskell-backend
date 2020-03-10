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
import Kore.Attribute.Pattern.FreeVariables
    ( freeVariable
    )
import Kore.Syntax.Variable
    ( Variable (..)
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )

import Test.Kore.Attribute.Parser
import qualified Test.Kore.Step.MockSymbols as Mock

parseConcrete
    :: FreeVariables Variable -> Attributes -> Parser (Concrete Variable)
parseConcrete freeVariables (Attributes attrs) =
    Foldable.foldlM
        (flip $ parseConcreteAttribute freeVariables )
        Default.def
        attrs

test_concrete :: TestTree
test_concrete =
    testCase "[concrete{}()] :: Concrete"
    $ expectSuccess Concrete { unConcrete = freeVars }
    $ parseConcrete freeVars $ Attributes [ concreteAttribute ]
  where
    freeVars = freeVariable (ElemVar Mock.x)

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
    $ parseConcrete freeVars
    $ Attributes [ concreteAttribute, concreteAttribute ]
  where
    freeVars = freeVariable (ElemVar Mock.x)

test_arguments :: TestTree
test_arguments =
    testCase "[concrete{}(\"illegal\")]"
        $ expectFailure
        $ parseConcrete freeVars $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern concreteSymbol [attributeString "illegal"]
    freeVars = freeVariable (ElemVar Mock.x)

test_parameters :: TestTree
test_parameters =
    testCase "[concrete{illegal}()]"
        $ expectFailure
        $ parseConcrete freeVars $ Attributes [ illegalAttribute ]
  where
    illegalAttribute =
        attributePattern_
            SymbolOrAlias
                { symbolOrAliasConstructor = concreteId
                , symbolOrAliasParams =
                    [ SortVariableSort (SortVariable "illegal") ]
                }
    freeVars = freeVariable (ElemVar Mock.x)
