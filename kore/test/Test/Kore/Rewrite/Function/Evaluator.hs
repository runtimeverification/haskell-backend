module Test.Kore.Rewrite.Function.Evaluator (test_evaluateApplication) where

import qualified Data.Map.Strict as Map
import Kore.Attribute.Synthetic (
    synthesize,
 )
import qualified Kore.Equation as Equation
import Kore.Internal.Condition (
    Condition,
 )
import qualified Kore.Internal.Condition as Condition
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.SideCondition as SideCondition (
    top,
 )
import Kore.Internal.TermLike (
    Application,
    Symbol,
    TermLike,
 )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Rewrite.Axiom.EvaluationStrategy as Kore
import qualified Kore.Rewrite.Axiom.Identifier as Axiom.Identifier
import qualified Kore.Rewrite.Function.Evaluator as Kore
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Simplify.Simplify as Kore
import Kore.Syntax.Application (
    Application (..),
 )
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import qualified Test.Kore.Simplify as Test
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
