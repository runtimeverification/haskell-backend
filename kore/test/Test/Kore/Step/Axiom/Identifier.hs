module Test.Kore.Step.Axiom.Identifier
    ( test_matchAxiomIdentifier ) where

import Test.Tasty
import Test.Tasty.HUnit

import qualified GHC.Stack as GHC

import           Kore.Internal.TermLike
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import           Kore.Syntax.Variable
                 ( Variable )

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions


test_matchAxiomIdentifier :: [TestTree]
test_matchAxiomIdentifier =
    [ matches "f(a)"
        (Mock.f Mock.a)
        (AxiomIdentifier.Application Mock.fId)
    , matches "inj(a)"
        (Mock.sortInjection10 Mock.a)
        (AxiomIdentifier.Application Mock.sortInjectionId)
    , matches "\\ceil(f(a))"
        (mkCeil_ (Mock.f Mock.a))
        (AxiomIdentifier.Ceil (AxiomIdentifier.Application Mock.fId))
    , notMatches "\\ceil(\\ceil(f(a)))" $ mkCeil_ (mkCeil_ (Mock.f Mock.a))
    , notMatches "\\and(f(a), g(a))" $ mkAnd (Mock.f Mock.a) (Mock.g Mock.a)
    , matches "x" (mkVar Mock.x) AxiomIdentifier.Variable
    ]

match
    :: GHC.HasCallStack
    => TestName
    -> TermLike Variable
    -> Maybe AxiomIdentifier
    -> TestTree
match name input expect =
    testCase name
    $ assertEqualWithExplanation "" expect
    $ AxiomIdentifier.matchAxiomIdentifier input

matches
    :: GHC.HasCallStack
    => TestName
    -> TermLike Variable
    -> AxiomIdentifier
    -> TestTree
matches name input expect = match ("matches " ++ name) input (Just expect)

notMatches
    :: GHC.HasCallStack
    => TestName
    -> TermLike Variable
    -> TestTree
notMatches name input = match ("does not match " ++ name) input Nothing
