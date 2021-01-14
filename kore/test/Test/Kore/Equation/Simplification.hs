module Test.Kore.Equation.Simplification
    ( test_simplifyEquation
    ) where

import Prelude.Kore

import Kore.Equation.Equation
import Kore.Equation.Simplification
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.TermLike

import Test.Kore.Equation.Common
    ( functionAxiomUnification_
    )
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
    ( runSimplifier
    )

import Test.Tasty
import Test.Tasty.HUnit.Ext

test_simplifyEquation :: [TestTree]
test_simplifyEquation =
    [ testGroup "Unify arguments"
        -- In all cases the argument gets simplified and substituted into the left term;
        -- the argument is then removed.
        [ testCase "Variable gets substituted in simplified equation" $ do
            let equation =
                    functionAxiomUnification_
                        Mock.fSymbol
                        [a]
                        a
                expected =
                    mkSimplifiedEquation (f a) a
                    & pure
                    & MultiAnd.make
            actual <- simplify equation
            assertEqual "" expected actual
        , testCase "Gets split into two equations" $ do
            let equation =
                    functionAxiomUnification_
                            Mock.fSymbol
                            [mkOr a b]
                            c
                expected =
                    [ mkSimplifiedEquation (f a) c
                    , mkSimplifiedEquation (f b) c
                    ]
                    & MultiAnd.make
            actual <- simplify equation
            assertEqual "" expected actual
        , testCase "Return original equation is any of the\
                    \ predicates from the simplified patterns\
                    \ is not \\top" $ do
            let equation =
                    functionAxiomUnification_
                            Mock.fMapSymbol
                            [mkOr symbolicMap xMap]
                            c
                expected = [equation] & MultiAnd.make
            actual <- simplify equation
            assertEqual "" expected actual
        ]
    -- TODO(ana.pantilie): after #2341 we should check that equations which
    --   don't have an 'argument' are not simplified
    ]

a, b, c, xMap, symbolicMap :: TermLike VariableName
a = Mock.a
b = Mock.b
c = Mock.c
f :: TermLike VariableName -> TermLike VariableName
f = Mock.f
xMap = mkElemVar Mock.xMap
symbolicMap =
    Mock.concatMap
        (Mock.elementMap
            (mkElemVar Mock.x)
            (mkElemVar Mock.y)
        )
        xMap

mkSimplifiedEquation
    :: TermLike VariableName
    -> TermLike VariableName
    -> Equation VariableName
mkSimplifiedEquation leftTerm rightTerm =
    mkEquation leftTerm rightTerm

simplify
    :: Equation VariableName
    -> IO (MultiAnd (Equation VariableName))
simplify equation =
    simplifyEquation equation
    & runSimplifier Mock.env
