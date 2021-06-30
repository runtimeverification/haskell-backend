{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Test.Kore.Builtin.AssocComm.CeilSimplifier (
    hprop_Builtin_Map,
    hprop_Builtin_Set,
    test_Builtin_Map,
    test_Builtin_Set,
) where

import Hedgehog hiding (
    test,
 )
import qualified Hedgehog.Gen as Gen
import Kore.Builtin.AssocComm.CeilSimplifier (
    generalizeMapElement,
 )
import Kore.Internal.Condition as Condition
import Kore.Internal.InternalMap
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    Predicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeForallPredicate,
    makeNotPredicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Simplify.Ceil as Ceil (
    makeEvaluate,
 )
import Prelude.Kore
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit.Ext

test_Builtin_Map :: [TestTree]
test_Builtin_Set :: [TestTree]
hprop_Builtin_Map :: Property
hprop_Builtin_Set :: Property
(hprop_Builtin_Map, hprop_Builtin_Set, test_Builtin_Map, test_Builtin_Set) =
    ( propertyBuiltinAssocComm
        (genKeys >>= traverse genMapElement)
        (Gen.subsequence opaqueMaps)
        fst
        defineMapElement
        mkNotMemberMap
        Mock.framedMap
    , propertyBuiltinAssocComm
        genKeys
        (Gen.subsequence opaqueSets)
        id
        defineSetElement
        mkNotMemberSet
        Mock.framedSet
    , testsMap
    , testsSet
    )
  where
    nullaryCtors = [Mock.a, Mock.b, Mock.c]
    elemVars = [Mock.xConfig, Mock.yConfig, Mock.zConfig]
    opaqueMaps@[opaqueMap1, opaqueMap2, opaqueMap3] =
        Mock.opaqueMap . mkElemVar <$> elemVars
    opaqueSets@[opaqueSet1, opaqueSet2, opaqueSet3] =
        Mock.opaqueSet . mkElemVar <$> elemVars
    genKeys = Gen.subsequence keys
    concreteKeys@[cKey1, cKey2, _] = nullaryCtors
    symbolicKeys@[sKey1, sKey2, _] = Mock.f . mkElemVar <$> elemVars
    keys = concreteKeys ++ symbolicKeys
    genMapElement key = (,) key <$> genVal
    genVal = Gen.element vals
    concreteVals@[cVal1, cVal2, _] = Mock.constr10 <$> nullaryCtors
    symbolicVals@[sVal1, sVal2, _] = Mock.g . mkElemVar <$> elemVars
    vals = concreteVals ++ symbolicVals
    cElt1 = (cKey1, cVal1)
    cElt2 = (cKey2, cVal2)
    sElt1 = (sKey1, cVal1)
    sElt2 = (sKey2, cVal2)

    defineMapElement (key, val) =
        -- symbolic keys are defined
        [makeCeilPredicate key | (not . isConcrete) key]
        ++
        -- symbolic values are defined
        [makeCeilPredicate val | (not . isConcrete) val]

    defineSetElement key =
        -- symbolic keys are defined
        [makeCeilPredicate key | (not . isConcrete) key]

    mkNotMemberMap (key, value) term =
        (makeForallPredicate variable . makeCeilPredicate)
            (Mock.framedMap [(key', value')] [term])
      where
        element = wrapElement (key, MapValue value)
        (variable, element') = generalizeMapElement (freeVariables term) element
        (key', MapValue value') = unwrapElement element'

    mkNotMemberSet key term = makeCeilPredicate (Mock.framedSet [key] [term])

    testsMap =
        [ let original = Mock.framedMap [(cKey1, sVal1)] []
              expect = [makeCeilPredicate sVal1]
           in test "values with concrete keys are defined" original expect
        , let original = Mock.framedMap [(sKey2, sVal2)] []
              expect =
                [ makeCeilPredicate sKey2
                , makeCeilPredicate sVal2
                ]
           in test "values with symbolic keys are defined" original expect
        , let original = Mock.framedMap [cElt1] []
              expect = []
           in test "concrete keys are defined by assumption" original expect
        , let original = Mock.framedMap [cElt1, cElt2] []
              expect = []
           in test "concrete keys are distinct by assumption" original expect
        , let original = Mock.framedMap [sElt1] []
              expect = [makeCeilPredicate sKey1]
           in test "symbolic keys are defined" original expect
        , let original = Mock.framedMap [cElt1, sElt1] []
              expect =
                [ makeCeilPredicate sKey1
                , makeNotEqualsPredicate cKey1 sKey1
                ]
           in test "symbolic and concrete keys are distinct" original expect
        , let original = Mock.framedMap [sElt1, sElt2] []
              expect =
                [ makeCeilPredicate sKey1
                , makeCeilPredicate sKey2
                , makeNotEqualsPredicate sKey1 sKey2
                ]
           in test "symbolic keys are distinct" original expect
        , let original = Mock.framedMap [cElt1] [opaqueMap1]
              expect =
                [ mkNotMemberMap cElt1 opaqueMap1
                , makeCeilPredicate opaqueMap1
                ]
           in test "concrete keys are not in the frame" original expect
        , let original = Mock.framedMap [sElt1] [opaqueMap1]
              expect =
                [ mkNotMemberMap sElt1 opaqueMap1
                , makeCeilPredicate sKey1
                , makeCeilPredicate opaqueMap1
                ]
           in test "symbolic keys are not in the frame" original expect
        , let original =
                Mock.framedMap [] [opaqueMap1, opaqueMap2, opaqueMap3]
              expect =
                map
                    makeCeilPredicate
                    [ Mock.framedMap [] [opaqueMap1, opaqueMap2]
                    , Mock.framedMap [] [opaqueMap1, opaqueMap3]
                    , Mock.framedMap [] [opaqueMap2, opaqueMap3]
                    , opaqueMap1
                    , opaqueMap2
                    , opaqueMap3
                    ]
           in test "frames are disjoint" original expect
        ]

    testsSet =
        [ let original = Mock.framedSet [cKey1] []
              expect = []
           in test "concrete keys are defined by assumption" original expect
        , let original = Mock.framedSet [cKey1, cKey2] []
              expect = []
           in test "concrete keys are distinct by assumption" original expect
        , let original = Mock.framedSet [sKey1] []
              expect = [makeCeilPredicate sKey1]
           in test "symbolic keys are defined" original expect
        , let original = Mock.framedSet [cKey1, sKey1] []
              expect =
                [ makeCeilPredicate sKey1
                , makeNotEqualsPredicate cKey1 sKey1
                ]
           in test "symbolic and concrete keys are distinct" original expect
        , let original = Mock.framedSet [sKey1, sKey2] []
              expect =
                [ makeCeilPredicate sKey1
                , makeCeilPredicate sKey2
                , makeNotEqualsPredicate sKey1 sKey2
                ]
           in test "symbolic keys are distinct" original expect
        , let original = Mock.framedSet [cKey1] [opaqueSet1]
              expect = map makeCeilPredicate [original, opaqueSet1]
           in test "concrete keys are not in the frame" original expect
        , let original = Mock.framedSet [sKey1] [opaqueSet1]
              expect =
                map makeCeilPredicate [original, sKey1, opaqueSet1]
           in test "symbolic keys are not in the frame" original expect
        , let original =
                Mock.framedSet [] [opaqueSet1, opaqueSet2, opaqueSet3]
              expect =
                map
                    makeCeilPredicate
                    [ Mock.framedSet [] [opaqueSet1, opaqueSet2]
                    , Mock.framedSet [] [opaqueSet1, opaqueSet3]
                    , Mock.framedSet [] [opaqueSet2, opaqueSet3]
                    , opaqueSet1
                    , opaqueSet2
                    , opaqueSet3
                    ]
           in test "frames are disjoint" original expect
        ]

    test ::
        HasCallStack =>
        TestName ->
        TermLike RewritingVariableName ->
        [Predicate RewritingVariableName] ->
        TestTree
    test testName original expect =
        testCase testName $ do
            actual <- makeEvaluate original
            assertEqual "" (MultiAnd.make expect) actual

propertyBuiltinAssocComm ::
    Show element =>
    Gen [element] ->
    Gen [TermLike RewritingVariableName] ->
    (element -> TermLike RewritingVariableName) ->
    (element -> [Predicate RewritingVariableName]) ->
    ( element ->
      TermLike RewritingVariableName ->
      Predicate RewritingVariableName
    ) ->
    ( [element] ->
      [TermLike RewritingVariableName] ->
      TermLike RewritingVariableName
    ) ->
    Property
propertyBuiltinAssocComm
    genElements
    genOpaques
    elementKey
    defineElement
    mkNotMember
    mkAssocComm =
        Hedgehog.property $ do
            opaques <- forAll genOpaques
            elements <- forAll genElements
            let original = mkAssocComm elements opaques
                keys = elementKey <$> elements
            actualPredicates <- (liftIO . makeEvaluate) original
            let expectDefinedElements = elements >>= defineElement

                expectDefinedOpaques = makeCeilPredicate <$> opaques

                expectDistinctKeys =
                    [ uncurry makeNotEqualsPredicate $ minMax key1 key2
                    | (key1, key2) <- zipWithTails (,) keys
                    , -- concrete keys are assumed to be distinct among the
                    -- concrete keys, but not among the symbolic keys
                    not (isConcrete key1 && isConcrete key2)
                    ]

                expectNoElementInOpaque =
                    [ mkNotMember element opaque'
                    | element <- elements
                    , opaque' <- opaques
                    ]

                expectDistinctOpaques =
                    [ makeCeilPredicate $ mkAssocComm [] [opaque1, opaque2]
                    | (opaque1, opaque2) <- zipWithTails (,) opaques
                    ]
                expectPredicates =
                    (MultiAnd.make . concat)
                        [ expectDefinedElements
                        , expectDefinedOpaques
                        , expectDistinctKeys
                        , expectNoElementInOpaque
                        , expectDistinctOpaques
                        ]
            expectPredicates === actualPredicates
      where
        zipWithTails :: (a -> a -> b) -> [a] -> [b]
        zipWithTails _ [] = []
        zipWithTails f (x : xs) = map (f x) xs ++ zipWithTails f xs

makeNotEqualsPredicate ::
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Predicate RewritingVariableName
makeNotEqualsPredicate x y =
    (makeNotPredicate . uncurry makeEqualsPredicate) (minMax x y)

makeEvaluate ::
    TermLike RewritingVariableName ->
    IO (MultiAnd (Predicate RewritingVariableName))
makeEvaluate termLike = do
    actualPattern <-
        makeEvaluate' termLike
            >>= (return . OrPattern.toPatterns)
            >>= expectSingleResult
    assertBool
        "expected \\top term"
        (isTop $ term actualPattern)
    assertBool
        "expected empty substitution"
        (Substitution.null $ substitution actualPattern)
    let actualPredicates =
            predicate actualPattern
                & Predicate.getMultiAndPredicate
                & MultiAnd.make
    return actualPredicates
  where
    makeEvaluate' =
        runSimplifier mockEnv
            . Ceil.makeEvaluate SideCondition.top
            . Pattern.fromTermLike
    mockEnv = Mock.env{simplifierAxioms = mempty}
    expectSingleResult =
        \case
            [actualPattern] -> return actualPattern
            _ -> assertFailure "expected single result"
