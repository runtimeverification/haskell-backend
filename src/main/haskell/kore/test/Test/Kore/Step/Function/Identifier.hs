module Test.Kore.Step.Function.Identifier where

import Test.Tasty
       ( TestTree )
import Test.Tasty.HUnit
       ( testCase )

import           Kore.AST.Common
                 ( Variable )
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.Valid
                 ( mkAnd, mkCeil_ )
import           Kore.Step.Function.Identifier
                 ( AxiomIdentifier )
import qualified Kore.Step.Function.Identifier as AxiomIdentifier
import           Kore.Step.Pattern
                 ( StepPattern )

import           Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import           Test.Tasty.HUnit.Extensions


test_axiomIdentifier :: [TestTree]
test_axiomIdentifier =
    [ Mock.f Mock.a `hasId` AxiomIdentifier.Application Mock.fId
    , Mock.sortInjection10 Mock.a
        `hasId` AxiomIdentifier.Application Mock.sortInjectionId
    , mkCeil_ (Mock.f Mock.a)
        `hasId` AxiomIdentifier.Ceil (AxiomIdentifier.Application Mock.fId)
    , hasNoId $ mkCeil_ (mkCeil_ (Mock.f Mock.a))
    , hasNoId $ mkAnd (Mock.f Mock.a) (Mock.g Mock.a)
    ]

hasId :: StepPattern Object Variable -> AxiomIdentifier Object -> TestTree
hasId input expected =
    testCase "AxiomId.extract evaluation"
        (assertEqualWithExplanation "has id"
            (Just expected)
            (AxiomIdentifier.extract input)
        )

hasNoId :: StepPattern Object Variable -> TestTree
hasNoId input =
    testCase "AxiomId.extract evaluation"
        (assertEqualWithExplanation "has no id"
            Nothing
            (AxiomIdentifier.extract input)
        )
