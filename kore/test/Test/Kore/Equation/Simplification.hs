module Test.Kore.Equation.Simplification (
    test_simplifyEquation,
) where

import Kore.Equation.Equation
import Kore.Equation.Simplification
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Prelude.Kore
import Test.Kore.Equation.Common (
    functionAxiomUnification_,
 )
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Simplify (
    testRunSimplifier,
 )
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_simplifyEquation :: [TestTree]
test_simplifyEquation =
    [ testGroup
        "Unify arguments"
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
                        & MultiAnd.singleton
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
        ]
    ]

a, b, c :: InternalVariable variable => TermLike variable
a = Mock.a
b = Mock.b
c = Mock.c
f :: TermLike RewritingVariableName -> TermLike RewritingVariableName
f = Mock.f

mkSimplifiedEquation ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Equation RewritingVariableName
mkSimplifiedEquation leftTerm rightTerm =
    mkEquation leftTerm rightTerm

simplify ::
    Equation RewritingVariableName ->
    IO (MultiAnd (Equation RewritingVariableName))
simplify equation =
    simplifyEquation equation
        & testRunSimplifier Mock.env
