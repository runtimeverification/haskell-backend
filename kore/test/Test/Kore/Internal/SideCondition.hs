module Test.Kore.Internal.SideCondition (
    TestSideCondition,
    module Kore.Internal.SideCondition,
    test_assumeDefined,
    test_isDefined,
    test_generateNormalizedAcs,
) where

import qualified Data.HashSet as HashSet
import Data.Maybe (
    fromJust,
 )
import Data.Sup (
    Sup (..),
 )
import GHC.Natural (
    Natural,
 )
import Kore.Internal.InternalMap (
    InternalMap,
 )
import Kore.Internal.InternalSet (
    InternalSet,
 )
import Kore.Internal.SideCondition
import Kore.Internal.TermLike
import Prelude.Kore
import Test.Kore (
    testId,
 )
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Tasty
import Test.Tasty.HUnit.Ext

type TestSideCondition = SideCondition VariableName

test_assumeDefined :: [TestTree]
test_assumeDefined =
    [ testCase "Fails on \\bottom" $ do
        let term :: TermLike VariableName
            term = mkBottom_
            actual = assumeDefined term
        assertEqual "" Nothing actual
    , testCase "Fails on nested \\bottom" $ do
        let term :: TermLike VariableName
            term = Mock.f mkBottom_
            actual = assumeDefined term
        assertEqual "" Nothing actual
    , testCase "And: implies subterms are defined" $ do
        let term :: TermLike VariableName
            term =
                mkAnd
                    Mock.plain00
                    (Mock.f Mock.a)
            expected =
                [term, Mock.plain00, Mock.f Mock.a]
                    & HashSet.fromList
                    & fromDefinedTerms
                    & Just
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "App: implies subterms are defined" $ do
        let term :: TermLike VariableName
            term =
                Mock.f (Mock.functional10 (Mock.g Mock.plain00))
            expected =
                [term, Mock.g Mock.plain00, Mock.plain00]
                    & HashSet.fromList
                    & fromDefinedTerms
                    & Just
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "Ceil: implies subterms are defined" $ do
        let term :: TermLike VariableName
            term = mkCeil_ Mock.plain00
            expected =
                [term, Mock.plain00]
                    & HashSet.fromList
                    & fromDefinedTerms
                    & Just
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "List: empty list is always defined" $ do
        let term :: TermLike VariableName
            term = Mock.builtinList []
            expected = fromDefinedTerms mempty & Just
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "List: implies subterms are defined" $ do
        let term :: TermLike VariableName
            term =
                Mock.builtinList
                    [ Mock.plain00
                    , Mock.plain00
                    , Mock.a
                    , Mock.f (Mock.g Mock.a)
                    ]
            expected =
                [ term
                , Mock.plain00
                , Mock.f (Mock.g Mock.a)
                , Mock.g Mock.a
                ]
                    & HashSet.fromList
                    & fromDefinedTerms
                    & Just
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "Forall: implies subterms are defined" $ do
        let term :: TermLike VariableName
            term =
                mkForall
                    Mock.x
                    ( mkForall
                        Mock.y
                        ( mkAnd
                            (Mock.f (mkElemVar Mock.x))
                            (Mock.g (mkElemVar Mock.y))
                        )
                    )
            expected =
                [ term
                , mkForall
                    Mock.y
                    ( mkAnd
                        (Mock.f (mkElemVar Mock.x))
                        (Mock.g (mkElemVar Mock.y))
                    )
                , mkAnd
                    (Mock.f (mkElemVar Mock.x))
                    (Mock.g (mkElemVar Mock.y))
                , Mock.f (mkElemVar Mock.x)
                , Mock.g (mkElemVar Mock.y)
                ]
                    & HashSet.fromList
                    & fromDefinedTerms
                    & Just
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "In: implies subterms are defined" $ do
        let term :: TermLike VariableName
            term =
                mkIn_
                    (Mock.f (mkElemVar Mock.x))
                    (Mock.functional10 (Mock.g Mock.a))
            expected =
                [ term
                , Mock.f (mkElemVar Mock.x)
                , Mock.g Mock.a
                ]
                    & HashSet.fromList
                    & fromDefinedTerms
                    & Just
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "Or: does not imply subterms are defined" $ do
        let term :: TermLike VariableName
            term =
                mkOr
                    Mock.plain00
                    (Mock.f Mock.a)
            expected =
                [term]
                    & HashSet.fromList
                    & fromDefinedTerms
                    & Just
            actual = assumeDefined term
        assertEqual "" expected actual
    , testCase "Empty collection is always defined" $ do
        let collection = Collection [] []
        testCollection collection [] []
    , testCase "Singleton with always defined key is always defined" $ do
        let collection =
                Collection
                    [(Mock.a, Mock.a)]
                    []
        testCollection collection [] []
    , testCase
        "Singleton without always defined key is defined if\
        \ key is defined"
        $ do
            let collection =
                    Collection
                        [(Mock.plain00, Mock.a)]
                        []
                expectedTerms = [Mock.plain00]
                expectedCollections = []
            testCollection collection expectedTerms expectedCollections
    , testCase "Opaque is always defined" $ do
        let collection = Collection [] [0]
        testCollection collection [] []
    , testCase "Assumes 2-element collection" $ do
        let collection =
                Collection
                    [ (Mock.f Mock.plain00, Mock.b)
                    , (mkElemVar Mock.x, Mock.a)
                    ]
                    []
            expectedTerms =
                [ Mock.plain00
                , Mock.f Mock.plain00
                ]
            expectedCollections = [collection]
        testCollection collection expectedTerms expectedCollections
    , testCase "Assumes 3-element, 1-opaque collection" $ do
        let collection =
                Collection
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.f Mock.plain00, Mock.b)
                    , (Mock.c, Mock.d)
                    ]
                    [0]
            expectedTerms =
                [ Mock.plain00
                , Mock.f Mock.plain00
                ]
            expectedCollections =
                [ Collection
                    [ (Mock.f Mock.plain00, Mock.b)
                    , (mkElemVar Mock.x, Mock.a)
                    ]
                    []
                , Collection
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.c, Mock.d)
                    ]
                    []
                , Collection
                    [ (mkElemVar Mock.x, Mock.a)
                    ]
                    [0]
                , Collection
                    [ (Mock.f Mock.plain00, Mock.b)
                    , (Mock.c, Mock.d)
                    ]
                    []
                , Collection
                    [ (Mock.f Mock.plain00, Mock.b)
                    ]
                    [0]
                , Collection
                    [ (Mock.c, Mock.d)
                    ]
                    [0]
                ]
        testCollection collection expectedTerms expectedCollections
    , testCase "Singleton map: assumes value is defined" $ do
        let testMap :: TermLike VariableName
            testMap =
                Mock.framedMap
                    [(Mock.a, Mock.f Mock.plain00)]
                    []
            expected =
                [ Mock.plain00
                , Mock.f Mock.plain00
                ]
                    & HashSet.fromList
                    & fromDefinedTerms
                    & Just
            actual = assumeDefined testMap
        assertEqual "" expected actual
    , testCase "2-element 1-opaque map: assumes values are also defined" $ do
        let testMap :: TermLike VariableName
            testMap =
                Mock.framedMap
                    [ (Mock.a, Mock.f Mock.plain00)
                    , (Mock.g Mock.a, Mock.f (mkElemVar Mock.x))
                    ]
                    [mkElemVar Mock.xMap]
            expected =
                [ Mock.plain00
                , Mock.f Mock.plain00
                , Mock.g Mock.a
                , Mock.f (mkElemVar Mock.x)
                , Mock.framedMap
                    [ (Mock.a, Mock.f Mock.plain00)
                    , (Mock.g Mock.a, Mock.f (mkElemVar Mock.x))
                    ]
                    []
                , Mock.framedMap
                    [(Mock.a, Mock.f Mock.plain00)]
                    [mkElemVar Mock.xMap]
                , Mock.framedMap
                    [(Mock.g Mock.a, Mock.f (mkElemVar Mock.x))]
                    [mkElemVar Mock.xMap]
                ]
                    & HashSet.fromList
                    & fromDefinedTerms
                    & Just
            actual = assumeDefined testMap
        assertEqual "" expected actual
    ]
  where
    testCollection input expectedTerms expectedCollections = do
        let testMap = collectionToMapTerm input
            testSet = collectionToSetTerm input
            expectedMaps = collectionToMapTerm <$> expectedCollections
            expectedSets = collectionToSetTerm <$> expectedCollections
            mapExpected =
                expectedTerms <> expectedMaps
                    & HashSet.fromList
                    & fromDefinedTerms
                    & Just
            setExpected =
                expectedTerms <> expectedSets
                    & HashSet.fromList
                    & fromDefinedTerms
                    & Just
            mapActual = assumeDefined testMap
            setActual = assumeDefined testSet
        assertEqual "Map" mapExpected mapActual
        assertEqual "Set" setExpected setActual

test_isDefined :: [TestTree]
test_isDefined =
    [ testCase
        "A functional symbol with always defined children\
        \ is always defined"
        $ do
            let term :: TermLike VariableName
                term = Mock.functional20 Mock.a (mkElemVar Mock.x)
                sideCondition = top
                actual = isDefined sideCondition term
            assertEqual "" True actual
    , testCase
        "A functional symbol application is assumed defined if\
        \ its subterms are assumed defined"
        $ do
            let term :: TermLike VariableName
                term = Mock.functional20 Mock.plain00 (Mock.f Mock.a)
                sideCondition =
                    [ Mock.plain00
                    , Mock.f Mock.a
                    ]
                        & HashSet.fromList
                        & fromDefinedTerms
                actual = isDefined sideCondition term
            assertEqual "" True actual
    , testCase "Singleton: collection is assumed to be defined" $ do
        let collection =
                Collection
                    [(Mock.plain00, Mock.a)]
                    []
        testCollection collection (Just collection) True
    , testCase
        "Singleton: always defined key implies\
        \ always defined collection"
        $ do
            let collection =
                    Collection
                        [ (mkElemVar Mock.x, Mock.a)
                        ]
                        []
            testCollection collection Nothing True
    , testCase
        "Singleton: not always defined key and map isn't assumed\
        \ to be defined"
        $ do
            let collection =
                    Collection
                        [ (Mock.f (mkElemVar Mock.x), Mock.a)
                        ]
                        []
            testCollection collection Nothing False
    , testCase "Opaque: opaque collection is always defined" $ do
        let collection = Collection [] [0]
        testCollection collection Nothing True
    , testCase "2-element: is assumed defined, is defined" $ do
        let collection =
                Collection
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.f Mock.plain00, Mock.b)
                    ]
                    []
        testCollection collection (Just collection) True
    , testCase "3-element: is assumed defined, is defined" $ do
        let collection =
                Collection
                    [ (mkElemVar Mock.x, Mock.a)
                    , (Mock.f Mock.plain00, Mock.b)
                    , (Mock.c, Mock.d)
                    ]
                    [0]
        testCollection collection (Just collection) True
    , testCase
        "3-element: is subcollection of assumed\
        \ to be defined collection"
        $ do
            let definedCollection =
                    Collection
                        [ (mkElemVar Mock.x, Mock.a)
                        , (Mock.f Mock.plain00, Mock.b)
                        , (Mock.c, Mock.d)
                        , (mkElemVar Mock.y, Mock.b)
                        ]
                        [0]
                collection =
                    Collection
                        [ (mkElemVar Mock.x, Mock.a)
                        , (Mock.f Mock.plain00, Mock.b)
                        , (Mock.c, Mock.d)
                        ]
                        []
            testCollection collection (Just definedCollection) True
    , testCase
        "3-element: is not subcollection of assumed\
        \ to be defined collection"
        $ do
            let definedCollection =
                    Collection
                        [ (mkElemVar Mock.x, Mock.a)
                        , (Mock.f Mock.plain00, Mock.b)
                        , (Mock.c, Mock.d)
                        , (mkElemVar Mock.y, Mock.b)
                        ]
                        [0]
                collection =
                    Collection
                        [ (mkElemVar Mock.x, Mock.a)
                        , (Mock.f Mock.plain00, Mock.b)
                        , (Mock.d, Mock.d)
                        ]
                        []
            testCollection collection (Just definedCollection) False
    , testCase "1-element concrete, opaque: is not always defined" $ do
        let collection =
                Collection
                    [(Mock.a, Mock.constr10 Mock.a)]
                    [0]
        testCollection collection Nothing False
    , testCase "1-element symbolic, opaque: is not always defined" $ do
        let collection =
                Collection
                    [(mkElemVar Mock.x, Mock.constr10 Mock.a)]
                    [0]
        testCollection collection Nothing False
    , testCase "Singleton map: value is not always defined" $ do
        let testMap :: TermLike VariableName
            testMap =
                Mock.framedMap
                    [(Mock.a, Mock.f Mock.plain00)]
                    []
            actual = isDefined top testMap
        assertBool "" (not actual)
    , testCase "2-element 1-opaque map: value is assumed defined" $ do
        let definedMap :: SideCondition VariableName
            definedMap =
                Mock.framedMap
                    [ (Mock.a, Mock.f Mock.plain00)
                    , (Mock.g Mock.a, Mock.f (mkElemVar Mock.x))
                    ]
                    [mkElemVar Mock.xMap]
                    & assumeDefined
                    & fromJust
            testTerm :: TermLike VariableName
            testTerm = Mock.plain00
            actual = isDefined definedMap testTerm
        assertBool "" actual
    ]
  where
    testCollection input maybeAssumeDefined expectedIsDefined = do
        let testMap = collectionToMapTerm input
            testSet = collectionToSetTerm input
            -- The tests assume that the defined part is
            -- well constructed (is not \\bottom)
            sideConditionMap =
                maybe
                    top
                    (fromJust . assumeDefined . collectionToMapTerm)
                    maybeAssumeDefined
            sideConditionSet =
                maybe
                    top
                    (fromJust . assumeDefined . collectionToSetTerm)
                    maybeAssumeDefined
            mapActual = isDefined sideConditionMap testMap
            setActual = isDefined sideConditionSet testSet
        assertEqual "Map" expectedIsDefined mapActual
        assertEqual "Set" expectedIsDefined setActual

test_generateNormalizedAcs :: [TestTree]
test_generateNormalizedAcs =
    [ testCase "Singleton symbolic: no subcollections to generate" $ do
        let collection =
                Collection
                    [(mkElemVar Mock.x, Mock.a)]
                    []
            expected = mempty
        testCollection collection expected
    , testCase "Singleton concrete: no subcollections to generate" $ do
        let collection =
                Collection
                    [(Mock.a, Mock.b)]
                    []
            expected = mempty
        testCollection collection expected
    , testCase "Singleton opaque: no subcollections to generate" $ do
        let collection = Collection [] [0]
            expected = mempty
        testCollection collection expected
    , testCase "2-element: generates itself" $ do
        let collection =
                Collection
                    [ (mkElemVar Mock.x, Mock.a)
                    , (mkElemVar Mock.y, Mock.b)
                    ]
                    []
            expected = [collection]
        testCollection collection expected
    , testCase "3-element symbolic: all unique pair-wise subcollections" $ do
        let collection =
                Collection
                    [ (mkElemVar Mock.x, Mock.a)
                    , (mkElemVar Mock.y, Mock.b)
                    , (mkElemVar Mock.z, Mock.c)
                    ]
                    []
            expected =
                [ Collection
                    [(mkElemVar Mock.x, Mock.a), (mkElemVar Mock.y, Mock.b)]
                    []
                , Collection
                    [(mkElemVar Mock.y, Mock.b), (mkElemVar Mock.z, Mock.c)]
                    []
                , Collection
                    [(mkElemVar Mock.x, Mock.a), (mkElemVar Mock.z, Mock.c)]
                    []
                ]
        testCollection collection expected
    , testCase "3-element concrete: all unique pair-wise subcollections" $ do
        let collection =
                Collection
                    [ (Mock.a, Mock.a)
                    , (Mock.b, Mock.b)
                    , (Mock.c, Mock.c)
                    ]
                    []
            expected =
                [ Collection
                    [(Mock.a, Mock.a), (Mock.b, Mock.b)]
                    []
                , Collection
                    [(Mock.b, Mock.b), (Mock.c, Mock.c)]
                    []
                , Collection
                    [(Mock.a, Mock.a), (Mock.c, Mock.c)]
                    []
                ]
        testCollection collection expected
    , testCase "3-opaque: all unique pair-wise subcollections" $ do
        let collection = Collection [] [0, 1, 2]
            expected =
                [ Collection
                    []
                    [0, 1]
                , Collection
                    []
                    [1, 2]
                , Collection
                    []
                    [0, 2]
                ]
        testCollection collection expected
    , testCase
        "2-concrete, 2-symbolic: generates all, including mixed,\
        \ unique pair-wise subcollections"
        $ do
            let collection =
                    Collection
                        [ (Mock.a, Mock.a)
                        , (mkElemVar Mock.x, Mock.b)
                        , (Mock.b, Mock.c)
                        , (mkElemVar Mock.y, Mock.d)
                        ]
                        []
                expected =
                    [ Collection
                        [(Mock.a, Mock.a), (mkElemVar Mock.x, Mock.b)]
                        []
                    , Collection
                        [(Mock.a, Mock.a), (Mock.b, Mock.c)]
                        []
                    , Collection
                        [(Mock.a, Mock.a), (mkElemVar Mock.y, Mock.d)]
                        []
                    , Collection
                        [(mkElemVar Mock.x, Mock.b), (Mock.b, Mock.c)]
                        []
                    , Collection
                        [(mkElemVar Mock.x, Mock.b), (mkElemVar Mock.y, Mock.d)]
                        []
                    , Collection
                        [(Mock.b, Mock.c), (mkElemVar Mock.y, Mock.d)]
                        []
                    ]
            testCollection collection expected
    , testCase
        "2-concrete 1-symbolic 1-opaque: all unique pairs\
        \ and every element-opaque pair"
        $ do
            let collection =
                    Collection
                        [ (Mock.a, Mock.a)
                        , (mkElemVar Mock.x, Mock.b)
                        , (Mock.b, Mock.c)
                        ]
                        [0]
                expected =
                    [ Collection
                        [(Mock.a, Mock.a), (mkElemVar Mock.x, Mock.b)]
                        []
                    , Collection
                        [(Mock.a, Mock.a), (Mock.b, Mock.c)]
                        []
                    , Collection
                        [(Mock.a, Mock.a)]
                        [0]
                    , Collection
                        [(mkElemVar Mock.x, Mock.b), (Mock.b, Mock.c)]
                        []
                    , Collection
                        [(mkElemVar Mock.x, Mock.b)]
                        [0]
                    , Collection
                        [(Mock.b, Mock.c)]
                        [0]
                    ]
            testCollection collection expected
    , testCase
        "2-symbolic 1-concrete 1-opaque map: all unique pairs\
        \ and every element-opaque pair"
        $ do
            let collection =
                    Collection
                        [ (Mock.a, Mock.a)
                        , (mkElemVar Mock.x, Mock.b)
                        , (mkElemVar Mock.y, Mock.c)
                        ]
                        [0]
                expected =
                    [ Collection
                        [(Mock.a, Mock.a), (mkElemVar Mock.x, Mock.b)]
                        []
                    , Collection
                        [(Mock.a, Mock.a), (mkElemVar Mock.y, Mock.c)]
                        []
                    , Collection
                        [(Mock.a, Mock.a)]
                        [0]
                    , Collection
                        [(mkElemVar Mock.x, Mock.b), (mkElemVar Mock.y, Mock.c)]
                        []
                    , Collection
                        [(mkElemVar Mock.x, Mock.b)]
                        [0]
                    , Collection
                        [(mkElemVar Mock.y, Mock.c)]
                        [0]
                    ]
            testCollection collection expected
    , testCase
        "3-element 2-opaque: all unique pairs\
        \ and all element-opaque pairs"
        $ do
            let collection =
                    Collection
                        [ (Mock.a, Mock.a)
                        , (mkElemVar Mock.x, Mock.b)
                        , (Mock.b, Mock.c)
                        ]
                        [0, 1]
                expected =
                    [ Collection
                        [(Mock.a, Mock.a), (mkElemVar Mock.x, Mock.b)]
                        []
                    , Collection
                        [(Mock.a, Mock.a), (Mock.b, Mock.c)]
                        []
                    , Collection
                        [(Mock.a, Mock.a)]
                        [0]
                    , Collection
                        [(Mock.a, Mock.a)]
                        [1]
                    , Collection
                        [(mkElemVar Mock.x, Mock.b), (Mock.b, Mock.c)]
                        []
                    , Collection
                        [(mkElemVar Mock.x, Mock.b)]
                        [0]
                    , Collection
                        [(mkElemVar Mock.x, Mock.b)]
                        [1]
                    , Collection
                        [(Mock.b, Mock.c)]
                        [0]
                    , Collection
                        [(Mock.b, Mock.c)]
                        [1]
                    , Collection
                        []
                        [0, 1]
                    ]
            testCollection collection expected
    ]
  where
    testCollection input expected = do
        let testMap = collectionToMap input
            testSet = collectionToSet input
            expectedMaps =
                HashSet.fromList $
                    collectionToMap
                        <$> expected
            expectedSets =
                HashSet.fromList $
                    collectionToSet
                        <$> expected
            actualMaps = generateNormalizedAcs testMap
            actualSets = generateNormalizedAcs testSet
        assertEqual "Maps" expectedMaps actualMaps
        assertEqual "Sets" expectedSets actualSets

collectionToMapTerm ::
    Collection VariableName ->
    TermLike VariableName
collectionToMapTerm = mkInternalMap . collectionToMap

collectionToMap ::
    Collection VariableName ->
    InternalMap Key (TermLike VariableName)
collectionToMap Collection{elements, opaqueVars} =
    Mock.framedInternalMap elements mapOpaqueVars
  where
    mapOpaqueVars = mkElemVar . mkTestMapVar <$> opaqueVars
    mkTestMapVar int =
        let counter = Just (Element int)
         in Mock.MockElementVariable (testId "xMap") counter Mock.mapSort

collectionToSetTerm ::
    Collection VariableName ->
    TermLike VariableName
collectionToSetTerm = mkInternalSet . collectionToSet

collectionToSet ::
    Collection VariableName ->
    InternalSet Key (TermLike VariableName)
collectionToSet Collection{elements, opaqueVars} =
    Mock.framedInternalSet setElements setOpaqueVars
  where
    setElements = fst <$> elements
    setOpaqueVars = mkElemVar . mkTestSetVar <$> opaqueVars
    mkTestSetVar int =
        let counter = Just (Element int)
         in Mock.MockElementVariable (testId "xSet") counter Mock.setSort

data Collection variable = Collection
    { elements :: [(TermLike variable, TermLike variable)]
    , opaqueVars :: [Natural]
    }
