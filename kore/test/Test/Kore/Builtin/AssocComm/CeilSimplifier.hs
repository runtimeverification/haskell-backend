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
import Hedgehog.Gen qualified as Gen
import Kore.Builtin.AssocComm.CeilSimplifier (
    generalizeMapElement,
 )
import Kore.Internal.InternalMap
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    Predicate,
    makeCeilPredicate,
    makeEqualsPredicate,
    makeForallPredicate,
    makeNotPredicate,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.TermLike as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Ceil qualified as Ceil (
    makeEvaluate,
 )
import Prelude.Kore
import Test.Kore.Rewrite.MockSymbols qualified as Mock
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
    concreteKeys@[cKey1, _, _] = nullaryCtors
    symbolicKeys@[sKey1, sKey2, _] = Mock.f . mkElemVar <$> elemVars
    keys = concreteKeys ++ symbolicKeys
    genMapElement key = (,) key <$> genVal
    genVal = Gen.element vals
    concreteVals@[cVal1, cVal2, _] = Mock.constr10 <$> nullaryCtors
    symbolicVals = Mock.g . mkElemVar <$> elemVars
    vals = concreteVals ++ symbolicVals
    sElt1 = (sKey1, cVal1)
    sElt2 = (sKey2, cVal2)

    defineMapElement (key, val) =
        -- symbolic keys are defined
        [makeCeilPredicate key | (not . isConcrete) key]
            ++
            -- symbolic values are defined
            [makeCeilPredicate val]

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
        [ let original = Mock.framedMap [sElt1, sElt2] [opaqueMap1]
              expect =
                [ makeCeilPredicate sKey1
                , makeCeilPredicate sKey2
                , makeCeilPredicate cVal1
                , makeCeilPredicate cVal2
                , makeCeilPredicate opaqueMap1
                , makeNotEqualsPredicate sKey1 sKey2
                , mkNotMemberMap sElt1 opaqueMap1
                , mkNotMemberMap sElt2 opaqueMap1
                ]
           in test "generates required definedness conditions" original expect
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
        , let original = Mock.framedMap [(Mock.b, Mock.constr10 Mock.a)] []
              expect = []
           in test "map is known to be defined" original expect
        ]

    testsSet =
        [ let original = Mock.framedSet [sKey1, sKey2] []
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
            when (isDefined original) discard
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

        isDefined = SideCondition.isDefined SideCondition.top

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
    makeEvaluate' termLike
        >>= expectSingleResult
  where
    makeEvaluate' =
        testRunSimplifier mockEnv
            . Ceil.makeEvaluate SideCondition.top
            . Pattern.fromTermLike
    mockEnv = Mock.env{axiomEquations = mempty}
    expectSingleResult result =
        case toList result of
            [actualPredicate] -> return actualPredicate
            _ -> assertFailure "expected single result"
