{-# OPTIONS_GHC -fno-warn-incomplete-uni-patterns #-}

module Test.Kore.Builtin.AssocComm.CeilSimplifier
    ( hprop_Builtin_Map
    , hprop_Builtin_Set
    , test_Builtin_Map
    , test_Builtin_Set
    ) where

import Prelude.Kore

import Hedgehog hiding
    ( test
    )
import qualified Hedgehog.Gen as Gen
import Test.Tasty

import Kore.Builtin.AssocComm.CeilSimplifier
    ( generalizeMapElement
    )
import Kore.Domain.Builtin as Domain
import Kore.Internal.Condition as Condition
import Kore.Internal.InternalMap
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    , makeCeilPredicate_
    , makeEqualsPredicate_
    , makeForallPredicate
    , makeNotPredicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import qualified Kore.Step.Simplification.Ceil as Ceil
    ( makeEvaluate
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
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
    elemVars = [Mock.x, Mock.y, Mock.z]
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
        [ makeCeilPredicate_ key | (not . isConcrete) key ]
        ++
        -- symbolic values are defined
        [ makeCeilPredicate_ val | (not . isConcrete) val ]

    defineSetElement key =
        -- symbolic keys are defined
        [ makeCeilPredicate_ key | (not . isConcrete) key ]

    mkNotMemberMap (key, value) term =
        (makeForallPredicate variable . makeCeilPredicate_)
            (Mock.framedMap [(key', value')] [term])
      where
        element = Domain.wrapElement (key, MapValue value)
        (variable, element') = generalizeMapElement (freeVariables term) element
        (key', MapValue value') = Domain.unwrapElement element'

    mkNotMemberSet key term = makeCeilPredicate_ (Mock.framedSet [key] [term])

    testsMap =
        [
            let
                original = Mock.framedMap [(cKey1, sVal1)] []
                expect = [makeCeilPredicate_ sVal1]
            in
                test "values with concrete keys are defined" original expect
        ,
            let
                original = Mock.framedMap [(sKey2, sVal2)] []
                expect =
                    [ makeCeilPredicate_ sKey2
                    , makeCeilPredicate_ sVal2
                    ]
            in
                test "values with symbolic keys are defined" original expect
        ,
            let
                original = Mock.framedMap [cElt1] []
                expect = []
            in
                test "concrete keys are defined by assumption" original expect
        ,
            let
                original = Mock.framedMap [cElt1, cElt2] []
                expect = []
            in
                test "concrete keys are distinct by assumption" original expect
        ,
            let
                original = Mock.framedMap [sElt1] []
                expect = [makeCeilPredicate_ sKey1]
            in
                test "symbolic keys are defined" original expect
        ,
            let
                original = Mock.framedMap [cElt1, sElt1] []
                expect =
                    [ makeCeilPredicate_ sKey1
                    , makeNotEqualsPredicate cKey1 sKey1
                    ]
            in
                test "symbolic and concrete keys are distinct" original expect
        ,
            let
                original = Mock.framedMap [sElt1, sElt2] []
                expect =
                    [ makeCeilPredicate_ sKey1
                    , makeCeilPredicate_ sKey2
                    , makeNotEqualsPredicate sKey1 sKey2
                    ]
            in
                test "symbolic keys are distinct" original expect
        ,
            let
                original = Mock.framedMap [cElt1] [opaqueMap1]
                expect =
                    [ mkNotMemberMap cElt1 opaqueMap1
                    , makeCeilPredicate_ opaqueMap1
                    ]
            in
                test "concrete keys are not in the frame" original expect
        ,
            let
                original = Mock.framedMap [sElt1] [opaqueMap1]
                expect =
                    [ mkNotMemberMap sElt1 opaqueMap1
                    , makeCeilPredicate_ sKey1
                    , makeCeilPredicate_ opaqueMap1
                    ]
            in
                test "symbolic keys are not in the frame" original expect
        ,
            let
                original =
                    Mock.framedMap [] [opaqueMap1, opaqueMap2, opaqueMap3]
                expect =
                    map makeCeilPredicate_
                        [ Mock.framedMap [] [opaqueMap1, opaqueMap2]
                        , Mock.framedMap [] [opaqueMap1, opaqueMap3]
                        , Mock.framedMap [] [opaqueMap2, opaqueMap3]
                        , opaqueMap1
                        , opaqueMap2
                        , opaqueMap3
                        ]
            in
                test "frames are disjoint" original expect
        ]

    testsSet =
        [
            let
                original = Mock.framedSet [cKey1] []
                expect = []
            in
                test "concrete keys are defined by assumption" original expect
        ,
            let
                original = Mock.framedSet [cKey1, cKey2] []
                expect = []
            in
                test "concrete keys are distinct by assumption" original expect
        ,
            let
                original = Mock.framedSet [sKey1] []
                expect = [makeCeilPredicate_ sKey1]
            in
                test "symbolic keys are defined" original expect
        ,
            let
                original = Mock.framedSet [cKey1, sKey1] []
                expect =
                    [ makeCeilPredicate_ sKey1
                    , makeNotEqualsPredicate cKey1 sKey1
                    ]
            in
                test "symbolic and concrete keys are distinct" original expect
        ,
            let
                original = Mock.framedSet [sKey1, sKey2] []
                expect =
                    [ makeCeilPredicate_ sKey1
                    , makeCeilPredicate_ sKey2
                    , makeNotEqualsPredicate sKey1 sKey2
                    ]
            in
                test "symbolic keys are distinct" original expect
        ,
            let
                original = Mock.framedSet [cKey1] [opaqueSet1]
                expect = map makeCeilPredicate_ [original, opaqueSet1]
            in
                test "concrete keys are not in the frame" original expect
        ,
            let
                original = Mock.framedSet [sKey1] [opaqueSet1]
                expect =
                    map makeCeilPredicate_ [original, sKey1, opaqueSet1]
            in
                test "symbolic keys are not in the frame" original expect
        ,
            let
                original =
                    Mock.framedSet [] [opaqueSet1, opaqueSet2, opaqueSet3]
                expect =
                    map makeCeilPredicate_
                        [ Mock.framedSet [] [opaqueSet1, opaqueSet2]
                        , Mock.framedSet [] [opaqueSet1, opaqueSet3]
                        , Mock.framedSet [] [opaqueSet2, opaqueSet3]
                        , opaqueSet1
                        , opaqueSet2
                        , opaqueSet3
                        ]
            in
                test "frames are disjoint" original expect
        ]

    test
        :: HasCallStack
        => TestName
        -> TermLike VariableName
        -> [Predicate VariableName]
        -> TestTree
    test testName original expect =
        testCase testName $ do
            actual <- makeEvaluate original
            assertEqual "" (MultiAnd.make expect) actual

propertyBuiltinAssocComm
    :: Show element
    => Gen [element]
    -> Gen [TermLike VariableName]
    -> (element -> TermLike VariableName)
    -> (element -> [Predicate VariableName])
    -> (element -> TermLike VariableName -> Predicate VariableName)
    -> ([element] -> [TermLike VariableName] -> TermLike VariableName)
    -> Property
propertyBuiltinAssocComm
    genElements
    genOpaques
    elementKey
    defineElement
    mkNotMember
    mkAssocComm
  = Hedgehog.property $ do
    opaques <- forAll genOpaques
    elements <- forAll genElements
    let original = mkAssocComm elements opaques
        keys = elementKey <$> elements
    actualPredicates <- (liftIO . makeEvaluate) original
    let -- | Elements are defined
        expectDefinedElements = elements >>= defineElement
        -- | Opaque operands are defined
        expectDefinedOpaques = makeCeilPredicate_ <$> opaques
        -- | Keys are distinct
        expectDistinctKeys =
            [ uncurry makeNotEqualsPredicate $ minMax key1 key2
            | (key1, key2) <- zipWithTails (,) keys
            -- concrete keys are assumed to be distinct among the
            -- concrete keys, but not among the symbolic keys
            , not (isConcrete key1 && isConcrete key2)
            ]
        -- | No element occurs in any opaque operand
        expectNoElementInOpaque =
            [ mkNotMember element opaque'
            | element <- elements
            , opaque' <- opaques
            ]
        -- | Opaque operands are distinct
        expectDistinctOpaques =
            [ makeCeilPredicate_ $ mkAssocComm [] [opaque1, opaque2]
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

makeNotEqualsPredicate
    :: TermLike VariableName
    -> TermLike VariableName
    -> Predicate VariableName
makeNotEqualsPredicate x y =
    (makeNotPredicate . uncurry makeEqualsPredicate_) (minMax x y)

makeEvaluate :: TermLike VariableName -> IO (MultiAnd (Predicate VariableName))
makeEvaluate termLike = do
    actualPattern <-
        makeEvaluate' termLike
        >>= (return . OrPattern.toPatterns)
        >>= expectSingleResult
    assertBool "expected \\top term"
        (isTop $ term actualPattern)
    assertBool "expected empty substitution"
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
    mockEnv = Mock.env { simplifierAxioms = mempty }
    expectSingleResult =
        \case
            [actualPattern] -> return actualPattern
            _ -> assertFailure "expected single result"
