module Test.Kore.Internal.SideCondition
    ( TestSideCondition
    , module Kore.Internal.SideCondition
    , test_assumeDefined
    ) where

import Prelude.Kore

import Test.Tasty

import qualified Data.HashSet as HashSet
import Kore.Internal.SideCondition
import Kore.Internal.TermLike

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Tasty.HUnit.Ext

type TestSideCondition = SideCondition VariableName

test_assumeDefined :: [TestTree]
test_assumeDefined =
    [ testCase "TESTING" $ do
        let term :: TermLike VariableName
            term =
                mkAnd
                    Mock.plain00
                    (Mock.plain10 Mock.a)
            expected =
                [term, Mock.plain00, Mock.plain10 Mock.a]
                & HashSet.fromList
                & fromDefinedTerms
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let term :: TermLike VariableName
            term =
                mkOr
                    Mock.plain00
                    (Mock.plain10 Mock.a)
            expected =
                [term]
                & HashSet.fromList
                & fromDefinedTerms
            actual = assumeDefined term
        assertEqual "" expected actual
    ]
