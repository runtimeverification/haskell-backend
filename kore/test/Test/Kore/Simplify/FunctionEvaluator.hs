module Test.Kore.Simplify.FunctionEvaluator (
    test_functionEvaluator,
) where

import Prelude.Kore
import Test.Tasty
import Test.Tasty.HUnit.Ext
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import qualified Kore.Rewrite.Axiom.Identifier as AxiomIdentifier
import qualified Data.Map.Strict as Map
import Kore.Internal.Symbol (Symbol)
import Kore.Internal.TermLike (TermLike)
import qualified Test.Kore.Internal.Pattern as Pattern
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
                                      )
import Kore.Internal.Predicate (Predicate)
import Kore.Equation
import Kore.Internal.From
import qualified Control.Lens as Lens
import Data.Generics.Product (
    field,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Simplify.FunctionEvaluator (evaluateFunctions)
import Test.Kore.Simplify
import qualified Kore.Internal.TermLike as TermLike
import Test.Kore.Equation.Common (
    functionAxiomUnification_,
 )

test_functionEvaluator :: [TestTree]
test_functionEvaluator =
    [ testCase "Applies one equation" $ do
        let term = Mock.f Mock.a
            axioms =
                [ (AxiomIdentifier.Application Mock.fId
                  , [ functionAxiomUnification_
                        Mock.fSymbol
                        [Mock.a]
                        Mock.b
                    , functionAxiomUnification_
                        Mock.fSymbol
                        [Mock.b]
                        Mock.c
                    ]
                  )
                ]
                & Map.fromList
            expected = Pattern.fromTermLike Mock.b
        actual <-
            evaluateFunctions
                SideCondition.top
                axioms
                term
            & runSimplifier Mock.env
        assertEqual "" expected actual
    , testCase "Applies two equations (nested)" $ do
        let term = Mock.f (Mock.functional10 (Mock.g Mock.a))
            axioms =
                [ (AxiomIdentifier.Application Mock.fId
                  , [ functionAxiomUnification_
                        Mock.fSymbol
                        [TermLike.mkElemVar Mock.xConfig]
                        Mock.c
                    ]
                  )
                , (AxiomIdentifier.Application Mock.gId
                  , [ functionAxiomUnification_
                        Mock.gSymbol
                        [Mock.a]
                        Mock.b
                    , functionAxiomUnification_
                        Mock.gSymbol
                        [Mock.b]
                        Mock.c
                    ]
                  )
                ]
                & Map.fromList
            expected = Pattern.fromTermLike Mock.c
        actual <-
            evaluateFunctions
                SideCondition.top
                axioms
                term
            & runSimplifier Mock.env
        assertEqual "" expected actual
    , testCase "Does multiple passes until stable result" $ do
        let term = Mock.f (Mock.functional10 (Mock.g Mock.a))
            axioms =
                [ (AxiomIdentifier.Application Mock.fId
                  , [ functionAxiomUnification_
                        Mock.fSymbol
                        [TermLike.mkElemVar Mock.xConfig]
                        Mock.c
                    ]
                  )
                , (AxiomIdentifier.Application Mock.gId
                  , [ functionAxiomUnification_
                        Mock.gSymbol
                        [Mock.a]
                        Mock.b
                    , functionAxiomUnification_
                        Mock.gSymbol
                        [Mock.b]
                        Mock.c
                    ]
                  )
                ]
                & Map.fromList
            expected = Pattern.fromTermLike Mock.c
        actual <-
            evaluateFunctions
                SideCondition.top
                axioms
                term
            & runSimplifier Mock.env
        assertEqual "" expected actual
    , testCase "Adds ensures to result" $ do
        let term = Mock.f Mock.a
            axioms =
                [ (AxiomIdentifier.Application Mock.fId
                  , [ functionDefinitionWithEnsures_
                        Mock.fSymbol
                        [Mock.a]
                        Mock.b
                        (fromEquals_
                            (Mock.h Mock.a)
                            Mock.c
                        )
                    , functionAxiomUnification_
                        Mock.fSymbol
                        [Mock.b]
                        Mock.c
                    ]
                  )
                ]
                & Map.fromList
            expected =
                Pattern.fromTermAndPredicate
                    Mock.b
                    (fromEquals_
                        (Mock.h Mock.a)
                        Mock.c
                    )
        actual <-
            evaluateFunctions
                SideCondition.top
                axioms
                term
            & runSimplifier Mock.env
        assertEqual "" expected actual
    ]

functionDefinitionWithEnsures_ ::
    Symbol ->
    [TermLike RewritingVariableName] ->
    TermLike RewritingVariableName ->
    Predicate RewritingVariableName ->
    Equation RewritingVariableName
functionDefinitionWithEnsures_ symbol args right ensures =
    functionAxiomUnification_ symbol args right
    & Lens.set (field @"ensures") ensures
