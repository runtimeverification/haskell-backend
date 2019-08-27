module Test.Kore.Step.Function.Evaluator
    ( test_evaluateApplication ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified Control.Lens as Lens
import           Data.Function
import           Data.Generics.Product
import qualified Data.Map.Strict as Map
import qualified GHC.Stack as GHC

import           Kore.Attribute.Hook
import           Kore.Attribute.Synthetic
                 ( synthesize )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Predicate
                 ( Predicate )
import qualified Kore.Internal.Predicate as Predicate
import           Kore.Internal.TermLike
                 ( Application, Symbol, TermLike, Variable )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Step.Axiom.Identifier as Axiom.Identifier
import qualified Kore.Step.Axiom.UserDefined as Axiom.UserDefined
import qualified Kore.Step.Function.Evaluator as Kore
import qualified Kore.Step.Rule as RulePattern
import qualified Kore.Step.Simplification.Data as Kore
import           Kore.Syntax.Application
                 ( Application (..) )

import qualified Test.Kore.Step.MockSymbols as Mock
import qualified Test.SMT as Test

test_evaluateApplication :: [TestTree]
test_evaluateApplication =
    [ evaluates "f(a) -- f(x) => x" (f a) a
    , notEvaluates "g(a) -- no axioms" (g a) id
    , notEvaluates "h(a) -- hooked, no axioms" (h a) TermLike.mkEvaluated
    ]
  where
    a = Mock.a
    evaluates
        :: GHC.HasCallStack
        => TestName
        -> Application Symbol (TermLike Variable)
        -> TermLike Variable
        -> TestTree
    evaluates name origin expect =
        testCase name $ do
            actual <- evaluateApplication Predicate.top origin
            assertEqual "" (OrPattern.fromTermLike expect) actual
    notEvaluates
        :: GHC.HasCallStack
        => TestName
        -> Application Symbol (TermLike Variable)
        -> (TermLike Variable -> TermLike Variable)
        -> TestTree
    notEvaluates name origin mkExpect =
        evaluates name origin (mkExpect $ mkApplySymbol origin)

fSymbol, gSymbol, hSymbol :: Symbol
fSymbol = Mock.fSymbol
gSymbol = Mock.gSymbol
hSymbol =
    Mock.hSymbol
    & Lens.set
        (field @"symbolAttributes" . field @"hook")
        (Hook $ Just "HOOK.missing")

f, g, h :: child -> Application Symbol child
f x = Application fSymbol [x]
g x = Application gSymbol [x]
h x = Application hSymbol [x]

mkApplySymbol :: Application Symbol (TermLike Variable) -> TermLike Variable
mkApplySymbol = synthesize . TermLike.ApplySymbolF

fEvaluator :: Kore.BuiltinAndAxiomSimplifier
fEvaluator =
    Kore.BuiltinAndAxiomSimplifier
    $ Axiom.UserDefined.equalityRuleEvaluator
    $ RulePattern.EqualityRule
    $ RulePattern.rulePattern left right
  where
    left = mkApplySymbol (f x)
    right = x
    x = TermLike.mkVar Mock.x

evaluateApplication
    :: Predicate Variable
    -> Application Symbol (TermLike Variable)
    -> IO (OrPattern Variable)
evaluateApplication predicate application =
    Test.runSMT
    $ Kore.evalSimplifier env
    $ Kore.evaluateApplication predicate application

simplifierAxioms :: Kore.BuiltinAndAxiomSimplifierMap
simplifierAxioms = Map.fromList [ (fId, fEvaluator) ]
  where
    fId = Axiom.Identifier.Application (TermLike.symbolConstructor fSymbol)

env :: Kore.Env
env = Mock.env { Kore.simplifierAxioms = simplifierAxioms }
