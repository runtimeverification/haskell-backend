module Test.Kore.Internal.SideCondition
    ( TestSideCondition
    , module Kore.Internal.SideCondition
    , test_assumeDefined
    , test_generateNormalizedAcs
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
    , testCase "TESTING" $ do
        let term :: TermLike VariableName
            term = Mock.framedMap [] []
            expected = fromDefinedTerms mempty
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let term :: TermLike VariableName
            term =
                Mock.framedMap
                    [(Mock.a, Mock.a)]
                    []
            expected = fromDefinedTerms mempty
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let term :: TermLike VariableName
            term =
                Mock.framedMap
                    [(Mock.plain00, Mock.a)]
                    []
            expected =
                [ term
                , Mock.plain00
                ]
                & HashSet.fromList
                & fromDefinedTerms
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let term :: TermLike VariableName
            term =
                Mock.framedMap
                    []
                    [mkElemVar Mock.xMap]
            expected = fromDefinedTerms mempty
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let term :: TermLike VariableName
            term =
                Mock.framedMap
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.f Mock.plain00, Mock.b)
                    ]
                    []
            expected =
                [ term
                , Mock.plain00
                , Mock.f Mock.plain00
                ]
                & HashSet.fromList
                & fromDefinedTerms
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let term :: TermLike VariableName
            term =
                Mock.framedMap
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.f Mock.plain00, Mock.b)
                    , (Mock.c, Mock.d)
                    ]
                    [mkElemVar Mock.xMap]
            expected =
                [ term
                , Mock.plain00
                , Mock.f Mock.plain00
                , Mock.framedMap
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.f Mock.plain00, Mock.b)
                    ]
                    []
                , Mock.framedMap
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.c, Mock.d)
                    ]
                    []
                , Mock.framedMap
                    [ (mkElemVar Mock.x, Mock.a)
                    ]
                    [mkElemVar Mock.xMap]
                , Mock.framedMap
                    [ (Mock.f Mock.plain00, Mock.b)
                    , (Mock.c, Mock.d)
                    ]
                    []
                , Mock.framedMap
                    [ (Mock.f Mock.plain00, Mock.b)
                    ]
                    [mkElemVar Mock.xMap]
                , Mock.framedMap
                    [ (Mock.c, Mock.d)
                    ]
                    [mkElemVar Mock.xMap]
                ]
                & HashSet.fromList
                & fromDefinedTerms
            actual = assumeDefined term
        assertEqual "" expected actual
    ]

test_generateNormalizedAcs :: [TestTree]
test_generateNormalizedAcs =
    [ testCase "TESTING" $ do
        let map' = Mock.framedInternalMap [(mkElemVar Mock.x, Mock.a)] []
            expected = mempty
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let map' = Mock.framedInternalMap [(Mock.a :: (TermLike Concrete), Mock.b)] []
            expected = mempty
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let map' = Mock.framedInternalMap [] [mkElemVar Mock.xMap]
            expected = mempty
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let map' = Mock.framedInternalMap [(mkElemVar Mock.x, Mock.a), (mkElemVar Mock.y, Mock.b)] []
            expected = mempty
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let map' =
                Mock.framedInternalMap
                [(mkElemVar Mock.x, Mock.a), (mkElemVar Mock.y, Mock.b), (mkElemVar Mock.z, Mock.c)]
                []
            expected =
                [ Mock.framedInternalMap
                    [(mkElemVar Mock.x, Mock.a), (mkElemVar Mock.y, Mock.b)]
                    []
                , Mock.framedInternalMap
                    [(mkElemVar Mock.y, Mock.b), (mkElemVar Mock.z, Mock.c)]
                    []
                , Mock.framedInternalMap
                    [(mkElemVar Mock.x, Mock.a), (mkElemVar Mock.z, Mock.c)]
                    []
                ]
                & HashSet.fromList
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let map' =
                Mock.framedInternalMap
                [(aConcrete, Mock.a), (bConcrete, Mock.b), (cConcrete, Mock.c)]
                []
            expected =
                [ Mock.framedInternalMap
                    [(aConcrete, Mock.a), (bConcrete, Mock.b)]
                    []
                , Mock.framedInternalMap
                    [(bConcrete, Mock.b), (cConcrete, Mock.c)]
                    []
                , Mock.framedInternalMap
                    [(aConcrete, Mock.a), (cConcrete, Mock.c)]
                    []
                ]
                & HashSet.fromList
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let map' =
                Mock.framedInternalMap
                []
                [mkElemVar Mock.xMap, mkElemVar Mock.yMap, mkElemVar Mock.zMap]
            expected =
                [ Mock.framedInternalMap
                    []
                    [mkElemVar Mock.xMap, mkElemVar Mock.yMap]
                , Mock.framedInternalMap
                    []
                    [mkElemVar Mock.yMap, mkElemVar Mock.zMap]
                , Mock.framedInternalMap
                    []
                    [mkElemVar Mock.xMap, mkElemVar Mock.zMap]
                ]
                & HashSet.fromList
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let map' =
                Mock.framedInternalMap
                [ (Mock.a, Mock.a)
                , (mkElemVar Mock.x, Mock.b)
                , (Mock.b, Mock.c)
                , (mkElemVar Mock.y, Mock.d)
                ]
                []
            expected =
                [ Mock.framedInternalMap
                    [(Mock.a, Mock.a), (mkElemVar Mock.x, Mock.b)]
                    []
                , Mock.framedInternalMap
                    [(Mock.a, Mock.a), (Mock.b, Mock.c)]
                    []
                , Mock.framedInternalMap
                    [(Mock.a, Mock.a), (mkElemVar Mock.y, Mock.d)]
                    []
                , Mock.framedInternalMap
                    [(mkElemVar Mock.x, Mock.b), (Mock.b, Mock.c)]
                    []
                , Mock.framedInternalMap
                    [(mkElemVar Mock.x, Mock.b), (mkElemVar Mock.y, Mock.d)]
                    []
                , Mock.framedInternalMap
                    [(Mock.b, Mock.c), (mkElemVar Mock.y, Mock.d)]
                    []
                ]
                & HashSet.fromList
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let map' =
                Mock.framedInternalMap
                [ (Mock.a, Mock.a)
                , (mkElemVar Mock.x, Mock.b)
                , (Mock.b, Mock.c)
                ]
                [mkElemVar Mock.xMap]
            expected =
                [ Mock.framedInternalMap
                    [(Mock.a, Mock.a), (mkElemVar Mock.x, Mock.b)]
                    []
                , Mock.framedInternalMap
                    [(Mock.a, Mock.a), (Mock.b, Mock.c)]
                    []
                , Mock.framedInternalMap
                    [(Mock.a, Mock.a)]
                    [mkElemVar Mock.xMap]
                , Mock.framedInternalMap
                    [(mkElemVar Mock.x, Mock.b), (Mock.b, Mock.c)]
                    []
                , Mock.framedInternalMap
                    [(mkElemVar Mock.x, Mock.b)]
                    [mkElemVar Mock.xMap]
                , Mock.framedInternalMap
                    [(Mock.b, Mock.c)]
                    [mkElemVar Mock.xMap]
                ]
                & HashSet.fromList
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let map' =
                Mock.framedInternalMap
                [ (Mock.a, Mock.a)
                , (mkElemVar Mock.x, Mock.b)
                , (mkElemVar Mock.y, Mock.c)
                ]
                [mkElemVar Mock.xMap]
            expected =
                [ Mock.framedInternalMap
                    [(Mock.a, Mock.a), (mkElemVar Mock.x, Mock.b)]
                    []
                , Mock.framedInternalMap
                    [(Mock.a, Mock.a), (mkElemVar Mock.y, Mock.c)]
                    []
                , Mock.framedInternalMap
                    [(Mock.a, Mock.a)]
                    [mkElemVar Mock.xMap]
                , Mock.framedInternalMap
                    [(mkElemVar Mock.x, Mock.b), (mkElemVar Mock.y, Mock.c)]
                    []
                , Mock.framedInternalMap
                    [(mkElemVar Mock.x, Mock.b)]
                    [mkElemVar Mock.xMap]
                , Mock.framedInternalMap
                    [(mkElemVar Mock.y, Mock.c)]
                    [mkElemVar Mock.xMap]
                ]
                & HashSet.fromList
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "TESTING" $ do
        let map' =
                Mock.framedInternalMap
                [ (Mock.a, Mock.a)
                , (mkElemVar Mock.x, Mock.b)
                , (Mock.b, Mock.c)
                ]
                [mkElemVar Mock.xMap, mkElemVar Mock.yMap]
            expected =
                [ Mock.framedInternalMap
                    [(Mock.a, Mock.a), (mkElemVar Mock.x, Mock.b)]
                    []
                , Mock.framedInternalMap
                    [(Mock.a, Mock.a), (Mock.b, Mock.c)]
                    []
                , Mock.framedInternalMap
                    [(Mock.a, Mock.a)]
                    [mkElemVar Mock.xMap]
                , Mock.framedInternalMap
                    [(Mock.a, Mock.a)]
                    [mkElemVar Mock.yMap]
                , Mock.framedInternalMap
                    [(mkElemVar Mock.x, Mock.b), (Mock.b, Mock.c)]
                    []
                , Mock.framedInternalMap
                    [(mkElemVar Mock.x, Mock.b)]
                    [mkElemVar Mock.xMap]
                , Mock.framedInternalMap
                    [(mkElemVar Mock.x, Mock.b)]
                    [mkElemVar Mock.yMap]
                , Mock.framedInternalMap
                    [(Mock.b, Mock.c)]
                    [mkElemVar Mock.xMap]
                , Mock.framedInternalMap
                    [(Mock.b, Mock.c)]
                    [mkElemVar Mock.yMap]
                , Mock.framedInternalMap
                    []
                    [mkElemVar Mock.xMap, mkElemVar Mock.yMap]
                ]
                & HashSet.fromList
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    ]

aConcrete, bConcrete, cConcrete :: TermLike Concrete
aConcrete = Mock.a
bConcrete = Mock.b
cConcrete = Mock.c
