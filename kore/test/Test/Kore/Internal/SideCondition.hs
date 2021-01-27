module Test.Kore.Internal.SideCondition
    ( TestSideCondition
    , module Kore.Internal.SideCondition
    , test_assumeDefined
    , test_isDefined
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
    [ testCase "And: implies subterms are defined" $ do
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
    , testCase "Or: does not imply subterms are defined" $ do
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
    , testCase "Map: empty map is always defined" $ do
        let term :: TermLike VariableName
            term = Mock.framedMap [] []
            expected = fromDefinedTerms mempty
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "Map: singleton with always defined key is always defined" $ do
        let term :: TermLike VariableName
            term =
                Mock.framedMap
                    [(Mock.a, Mock.a)]
                    []
            expected = fromDefinedTerms mempty
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "Map: singleton without always defined key" $ do
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
    , testCase "Map: opaque map is always defined" $ do
        let term :: TermLike VariableName
            term =
                Mock.framedMap
                    []
                    [mkElemVar Mock.xMap]
            expected = fromDefinedTerms mempty
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "Map: assumes 2-element map" $ do
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
    , testCase "Map: assumes 3-element, 1-opaque map" $ do
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

test_isDefined :: [TestTree]
test_isDefined =
    [ testCase "Singleton map: always defined key implies always defined map" $ do
        let term =
                Mock.framedMap
                    [ (mkElemVar Mock.x, Mock.a)
                    ]
                    []
            sideCondition = top
            actual = isDefined sideCondition term
        assertEqual "" True actual
    , testCase "Singleton map: not always defined key and map isn't assumed\
                \ to be defined" $ do
        let term =
                Mock.framedMap
                    [ (Mock.f (mkElemVar Mock.x), Mock.a)
                    ]
                    []
            sideCondition = top
            actual = isDefined sideCondition term
        assertEqual "" False actual
    , testCase "Opaque map: opaque map is always defined" $ do
        let term =
                Mock.framedMap
                    []
                    [mkElemVar Mock.xMap]
            sideCondition = top
            actual = isDefined sideCondition term
        assertEqual "" True actual
    , testCase "2-element map: is assumed defined, is defined" $ do
        let defined =
                Mock.framedMap
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.f Mock.plain00, Mock.b)
                    ]
                    []
            term =
                Mock.framedMap
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.f Mock.plain00, Mock.b)
                    ]
                    []
            sideCondition = assumeDefined defined
            actual = isDefined sideCondition term
        assertEqual "" True actual
    , testCase "3-element map: is submap of assumed to be defined map" $ do
        let defined =
                Mock.framedMap
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.f Mock.plain00, Mock.b)
                    , (Mock.c, Mock.d)
                    , (mkElemVar Mock.y, Mock.b)
                    ]
                    [mkElemVar Mock.xMap]
            term =
                Mock.framedMap
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.f Mock.plain00, Mock.b)
                    , (Mock.c, Mock.d)
                    ]
                    []
            sideCondition = assumeDefined defined
            actual = isDefined sideCondition term
        assertEqual "" True actual
    , testCase "3-element map: is not submap of assumed to be defined map" $ do
        let defined =
                Mock.framedMap
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.f Mock.plain00, Mock.b)
                    , (Mock.c, Mock.d)
                    , (mkElemVar Mock.y, Mock.b)
                    ]
                    [mkElemVar Mock.xMap]
            term =
                Mock.framedMap
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.f Mock.plain00, Mock.b)
                    , (Mock.d, Mock.d)
                    ]
                    []
            sideCondition = assumeDefined defined
            actual = isDefined sideCondition term
        assertEqual "" False actual
    ]

test_generateNormalizedAcs :: [TestTree]
test_generateNormalizedAcs =
    [ testCase "Singleton symbolic map: no submaps to generate" $ do
        let map' =
                Mock.framedInternalMap
                    [(mkElemVar Mock.x, Mock.a)]
                    []
            expected = mempty
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "Singleton concrete map: no submaps to generate" $ do
        let map' =
                Mock.framedInternalMap
                    [(aConcrete, Mock.b)]
                    []
            expected = mempty
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "Singleton opaque map: no submaps to generate" $ do
        let map' = Mock.framedInternalMap [] [mkElemVar Mock.xMap]
            expected = mempty
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "2-element map: no submaps to generate" $ do
        let map' =
                Mock.framedInternalMap
                    [ (mkElemVar Mock.x, Mock.a)
                    , (mkElemVar Mock.y, Mock.b)
                    ]
                    []
            expected = mempty
            actual = generateNormalizedAcs map'
        assertEqual "" expected actual
    , testCase "3-element symbolic map: all unique pair-wise submaps" $ do
        let map' =
                Mock.framedInternalMap
                    [ (mkElemVar Mock.x, Mock.a)
                    , (mkElemVar Mock.y, Mock.b)
                    , (mkElemVar Mock.z, Mock.c)
                    ]
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
    , testCase "3-element concrete map: all unique pair-wise submaps" $ do
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
    , testCase "3-opaque map: all unique pair-wise submaps" $ do
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
    , testCase "2-concrete, 2-symbolic map: generates all, including mixed,\
                \ unique pair-wise submaps" $ do
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
    , testCase "2-concrete 1-symbolic 1-opaque map: all unique pairs\
                \ and every element-opaque pair" $ do
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
    , testCase "2-symbolic 1-concrete 1-opaque map: all unique pairs\
                \ and every element-opaque pair" $ do
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
    , testCase "3-element 2-opaque: all unique pairs\
                \ and all element-opaque pairs" $ do
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
