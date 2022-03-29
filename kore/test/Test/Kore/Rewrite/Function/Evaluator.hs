module Test.Kore.Rewrite.Function.Evaluator (test_evaluateApplication) where

import Data.Map.Strict qualified as Map
import Kore.Attribute.Synthetic (
    synthesize,
 )
import Kore.Equation qualified as Equation
import Kore.Internal.Condition (
    Condition,
 )
import Kore.Internal.Condition qualified as Condition
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.SideCondition qualified as SideCondition (
    top,
 )
import Kore.Internal.TermLike (
    Application,
    Symbol,
    TermLike,
 )
import Kore.Internal.TermLike qualified as TermLike
import Kore.Rewrite.Axiom.EvaluationStrategy qualified as Kore
import Kore.Rewrite.Axiom.Identifier qualified as Axiom.Identifier
import Kore.Rewrite.Function.Evaluator qualified as Kore
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify qualified as Kore
import Kore.Syntax.Application (
    Application (..),
 )
import Prelude.Kore
import Test.Kore.Rewrite.MockSymbols qualified as Mock
import Test.Kore.Simplify qualified as Test
import Test.Tasty
import Test.Tasty.HUnit

test_evaluateApplication :: [TestTree]
test_evaluateApplication =
    [ evaluates "f(a) -- f(x) => x" (f a) a
    , notEvaluates "g(a) -- no axioms" (g a) id
    ]
  where
    a = Mock.a
    evaluates ::
        HasCallStack =>
        TestName ->
        Application Symbol (TermLike RewritingVariableName) ->
        TermLike RewritingVariableName ->
        TestTree
    evaluates name origin expect =
        makeTest
            name
            origin
            (OrPattern.fromTermLike expect)
    notEvaluates ::
        HasCallStack =>
        TestName ->
        Application Symbol (TermLike RewritingVariableName) ->
        (TermLike RewritingVariableName -> TermLike RewritingVariableName) ->
        TestTree
    notEvaluates name origin mkExpect =
        makeTest
            name
            origin
            (OrPattern.fromTermLike $ mkExpect $ mkApplySymbol origin)

    makeTest ::
        HasCallStack =>
        TestName ->
        Application Symbol (TermLike RewritingVariableName) ->
        OrPattern RewritingVariableName ->
        TestTree
    makeTest name origin expect =
        testCase name $ do
            actual <- evaluateApplication Condition.top origin
            assertEqual "" expect actual

fSymbol, gSymbol :: Symbol
fSymbol = Mock.fSymbol
gSymbol = Mock.gSymbol

f, g :: child -> Application Symbol child
f x = Application fSymbol [x]
g x = Application gSymbol [x]

mkApplySymbol ::
    Application Symbol (TermLike RewritingVariableName) ->
    TermLike RewritingVariableName
mkApplySymbol = synthesize . TermLike.ApplySymbolF

mkApplySymbol' ::
    Application Symbol (TermLike RewritingVariableName) ->
    TermLike RewritingVariableName
mkApplySymbol' = synthesize . TermLike.ApplySymbolF

fEvaluator :: Kore.BuiltinAndAxiomSimplifier
fEvaluator =
    Kore.simplificationEvaluation $
        Equation.mkEquation left right
  where
    left = mkApplySymbol' (f x)
    right = x
    x = TermLike.mkElemVar Mock.xConfig

evaluateApplication ::
    Condition RewritingVariableName ->
    Application Symbol (TermLike RewritingVariableName) ->
    IO (OrPattern RewritingVariableName)
evaluateApplication predicate =
    Test.runSimplifier env
        . Kore.evaluateApplication SideCondition.top predicate

simplifierAxioms :: Kore.BuiltinAndAxiomSimplifierMap
simplifierAxioms = Map.fromList [(fId, fEvaluator)]
  where
    fId = Axiom.Identifier.Application (TermLike.symbolConstructor fSymbol)

env :: Test.Env (Test.SimplifierT Test.NoSMT)
env = Mock.env{Test.simplifierAxioms = simplifierAxioms}
