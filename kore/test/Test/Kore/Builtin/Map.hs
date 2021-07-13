module Test.Kore.Builtin.Map (
    test_lookupUnit,
    test_lookupUpdate,
    test_removeUnit,
    test_sizeUnit,
    test_removeKeyNotIn,
    test_removeKeyIn,
    test_removeAllMapUnit,
    test_removeAllSetUnit,
    test_removeAll,
    test_concatUnit,
    test_lookupConcatUniqueKeys,
    test_concatDuplicateKeys,
    test_concatCommutes,
    test_concatAssociates,
    test_inKeysUnit,
    test_keysUnit,
    test_keysElement,
    test_keys,
    test_keysListUnit,
    test_keysListElement,
    test_keysList,
    test_inKeysElement,
    test_values,
    test_inclusion,
    test_simplify,
    test_symbolic,
    test_isBuiltin,
    test_unifyConcrete,
    test_unifyEmptyWithEmpty,
    test_unifySelectFromEmpty,
    test_unifySelectFromSingleton,
    test_unifySelectSingletonFromSingleton,
    test_unifySelectFromSingletonWithoutLeftovers,
    test_unifySelectFromTwoElementMap,
    test_unifySelectTwoFromTwoElementMap,
    test_unifySameSymbolicKey,
    test_unifySameSymbolicKeySymbolicOpaque,
    test_concretizeKeys,
    test_renormalize,
    test_concretizeKeysAxiom,
    hprop_unparse,
    test_inKeys,
    --
    normalizedMap,
    asInternal,
) where

import Control.Error (
    runMaybeT,
 )
import Control.Monad (
    guard,
 )
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Default as Default
import Data.HashMap.Strict (
    HashMap,
 )
import qualified Data.HashMap.Strict as HashMap
import qualified Data.HashSet as HashSet
import qualified Data.List as List
import qualified Data.Maybe as Maybe (
    fromJust,
 )
import qualified Data.Reflection as Reflection
import Hedgehog (
    Gen,
    Property,
    PropertyT,
    discard,
    forAll,
    (===),
 )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Map as Map
import qualified Kore.Builtin.Map.Map as Map
import Kore.Internal.InternalMap
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.Pattern
import Kore.Internal.Predicate (
    makeCeilPredicate,
    makeMultipleAndPredicate,
    makeTruePredicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike hiding (
    asConcrete,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    configElementVariableFromId,
    mkConfigVariable,
    ruleElementVariableFromId,
 )
import Kore.Rewrite.RulePattern
import Prelude.Kore hiding (
    concatMap,
 )
import SMT (
    NoSMT,
 )
import Test.Expect
import Test.Kore (
    configElementVariableGen,
    standaloneGen,
    testId,
 )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Kore.Builtin.Int (
    genInteger,
    genIntegerKey,
    genIntegerPattern,
 )
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Builtin.List as Test.List
import qualified Test.Kore.Builtin.Set as Test.Set
import qualified Test.Kore.Internal.OrPattern as OrPattern
import qualified Test.Kore.Rewrite.MockSymbols as Mock
import Test.Kore.Simplify (
    runSimplifier,
 )
import Test.SMT
import Test.Tasty
import Test.Tasty.HUnit.Ext

genMapInteger :: Gen a -> Gen (HashMap Integer a)
genMapInteger genElement =
    Gen.list (Range.linear 0 32) ((,) <$> genInteger <*> genElement)
        <&> HashMap.fromList

genConcreteMap :: Gen a -> Gen (HashMap Key a)
genConcreteMap genElement =
    mapKeys Test.Int.asKey <$> genMapInteger genElement

genMapPattern :: Gen (TermLike RewritingVariableName)
genMapPattern = asTermLike <$> genConcreteMap genIntegerPattern

genMapSortedVariable ::
    Sort -> Gen a -> Gen (HashMap (ElementVariable RewritingVariableName) a)
genMapSortedVariable sort genElement =
    Gen.list
        (Range.linear 0 32)
        ( (,)
            <$> standaloneGen (configElementVariableGen sort)
            <*> genElement
        )
        <&> HashMap.fromList

test_lookupUnit :: [TestTree]
test_lookupUnit =
    [ testPropertyWithoutSolver "lookup{}(unit{}(), key) === \\bottom{}()" $ do
        key <- forAll genIntegerPattern
        let patLookup = lookupMap unitMap key
            predicate = mkEquals_ mkBottom_ patLookup
        (===) OrPattern.bottom =<< evaluateT patLookup
        (===) OrPattern.top =<< evaluateT predicate
    , testPropertyWithoutSolver "lookupOrDefault{}(unit{}(), key, default) === default" $ do
        key <- forAll genIntegerPattern
        def <- forAll genIntegerPattern
        let patLookup = lookupOrDefaultMap unitMap key def
            predicate = mkEquals_ def patLookup
        (===) (OrPattern.fromTermLike def) =<< evaluateT patLookup
        (===) OrPattern.top =<< evaluateT predicate
    ]

test_lookupUpdate :: [TestTree]
test_lookupUpdate =
    [ testPropertyWithoutSolver "lookup{}(update{}(map, key, val), key) === val" $ do
        patKey <- forAll genIntegerPattern
        patVal <- forAll genIntegerPattern
        patMap <- forAll genMapPattern
        let patLookup = lookupMap (updateMap patMap patKey patVal) patKey
            predicate = mkEquals_ patLookup patVal
            expect = OrPattern.fromTermLike patVal
        (===) expect =<< evaluateT patLookup
        (===) OrPattern.top =<< evaluateT predicate
    , testPropertyWithoutSolver "lookupOrDefault{}(update{}(map, key, val), key, def) === val" $ do
        patKey <- forAll genIntegerPattern
        patDef <- forAll genIntegerPattern
        patVal <- forAll genIntegerPattern
        patMap <- forAll genMapPattern
        let patUpdate = updateMap patMap patKey patVal
            patLookup = lookupOrDefaultMap patUpdate patKey patDef
            predicate = mkEquals_ patLookup patVal
            expect = OrPattern.fromTermLike patVal
        (===) expect =<< evaluateT patLookup
        (===) OrPattern.top =<< evaluateT predicate
    ]

test_removeUnit :: TestTree
test_removeUnit =
    testPropertyWithSolver
        "remove{}(unit{}(), key) === unit{}()"
        ( do
            key <- forAll genIntegerPattern
            let patRemove = removeMap unitMap key
                predicate = mkEquals_ unitMap patRemove
            expect <- evaluateT unitMap
            (===) expect =<< evaluateT patRemove
            (===) OrPattern.top =<< evaluateT predicate
        )

test_sizeUnit :: TestTree
test_sizeUnit =
    testPropertyWithSolver
        "MAP.size is size"
        ( do
            someMap <- forAll $ genConcreteMap genIntegerPattern
            let size = HashMap.size someMap
                patExpected = Test.Int.asInternal $ toInteger size
                patActual =
                    mkApplySymbol
                        sizeMapSymbol
                        [asTermLike someMap]
                predicate = mkEquals_ patExpected patActual
            expect <- evaluateT patExpected
            (===) expect =<< evaluateT patActual
            (===) OrPattern.top =<< evaluateT predicate
        )

test_removeKeyNotIn :: TestTree
test_removeKeyNotIn =
    testPropertyWithSolver
        "MAP.remove key with key not in map"
        ( do
            key <- forAll genIntegerPattern
            map' <- forAll genMapPattern
            isInMap <- evaluateT $ lookupMap map' key
            unless (OrPattern.bottom == isInMap) discard
            let patRemove = removeMap map' key
                predicate = mkEquals_ map' patRemove
            expect <- evaluateT map'
            (===) expect =<< evaluateT patRemove
            (===) OrPattern.top =<< evaluateT predicate
        )

test_removeKeyIn :: TestTree
test_removeKeyIn =
    testPropertyWithSolver
        "MAP.remove key with key in map"
        ( do
            key <- forAll genIntegerPattern
            val <- forAll genIntegerPattern
            map' <- forAll genMapPattern
            isInMap <- evaluateT $ lookupMap map' key
            unless (OrPattern.bottom == isInMap) discard
            let patRemove = removeMap (updateMap map' key val) key
                predicate = mkEquals_ patRemove map'
            expect <- evaluateT map'
            (===) expect =<< evaluateT patRemove
            (===) OrPattern.top =<< evaluateT predicate
        )

test_removeAllMapUnit :: TestTree
test_removeAllMapUnit =
    testPropertyWithSolver
        "removeAll{}(unit{}(), set) === unit{}()"
        ( do
            set <- forAll Test.Set.genSetPattern
            let patRemoveAll = removeAllMap unitMap set
                predicate = mkEquals_ unitMap patRemoveAll
            expect <- evaluateT unitMap
            (===) expect =<< evaluateT patRemoveAll
            (===) OrPattern.top =<< evaluateT predicate
        )

test_removeAllSetUnit :: TestTree
test_removeAllSetUnit =
    testPropertyWithSolver
        "removeAll{}(map, unit{}()) === map"
        ( do
            map' <- forAll genMapPattern
            let patRemoveAll = removeAllMap map' unitSet
                predicate = mkEquals_ map' patRemoveAll
            expect <- evaluateT map'
            (===) expect =<< evaluateT patRemoveAll
            (===) OrPattern.top =<< evaluateT predicate
        )

test_removeAll :: TestTree
test_removeAll =
    testPropertyWithSolver
        "MAP.removeAll and MAP.remove"
        ( do
            map' <- forAll genMapPattern
            set <- forAll Test.Set.genSetConcreteIntegerPattern
            when (set == HashSet.empty) discard
            let key = head (HashSet.toList set)
                diffSet = HashSet.delete key set
                patSet = mkSet_ set & fromConcrete
                patDiffSet = mkSet_ diffSet & fromConcrete
                patKey = fromConcrete key
                patRemoveAll1 = removeAllMap map' patSet
                patRemoveAll2 =
                    removeAllMap
                        (removeMap map' patKey)
                        patDiffSet
                predicate = mkEquals_ patRemoveAll1 patRemoveAll2
            expect <- evaluateT patRemoveAll2
            (===) expect =<< evaluateT patRemoveAll1
            (===) OrPattern.top =<< evaluateT predicate
        )

test_concatUnit :: TestTree
test_concatUnit =
    testPropertyWithSolver
        "concat{}(unit{}(), map) === concat{}(map, unit{}()) === map"
        ( do
            patMap <- forAll genMapPattern
            let patConcat2 = concatMap patUnit patMap
                patConcat1 = concatMap patMap patUnit
                patUnit = unitMap
                predicate1 = mkEquals_ patMap patConcat1
                predicate2 = mkEquals_ patMap patConcat2
            expect <- evaluateT patMap
            (===) expect =<< evaluateT patConcat1
            (===) expect =<< evaluateT patConcat2
            (===) OrPattern.top =<< evaluateT predicate1
            (===) OrPattern.top =<< evaluateT predicate2
        )

test_lookupConcatUniqueKeys :: TestTree
test_lookupConcatUniqueKeys =
    testPropertyWithSolver
        "MAP.lookup with two unique keys"
        ( do
            patKey1 <- forAll genIntegerPattern
            patKey2 <- forAll genIntegerPattern
            when (patKey1 == patKey2) discard
            patVal1 <- forAll genIntegerPattern
            patVal2 <- forAll genIntegerPattern
            let patConcat = concatMap patMap1 patMap2
                patMap1 = elementMap patKey1 patVal1
                patMap2 = elementMap patKey2 patVal2
                patLookup1 = lookupMap patConcat patKey1
                patLookup2 = lookupMap patConcat patKey2
                predicate =
                    mkImplies
                        (mkNot (mkEquals_ patKey1 patKey2))
                        ( mkAnd
                            (mkEquals_ patLookup1 patVal1)
                            (mkEquals_ patLookup2 patVal2)
                        )
                expect1 = OrPattern.fromTermLike patVal1
                expect2 = OrPattern.fromTermLike patVal2
            (===) expect1 =<< evaluateT patLookup1
            (===) expect2 =<< evaluateT patLookup2
            (===) OrPattern.top =<< evaluateT predicate
        )

test_concatDuplicateKeys :: TestTree
test_concatDuplicateKeys =
    testPropertyWithSolver
        "concat{}(element{}(key, val1), element{}(key, val2)) === \\bottom{}()"
        ( do
            patKey <- forAll genIntegerPattern
            patVal1 <- forAll genIntegerPattern
            patVal2 <- forAll genIntegerPattern
            let patMap1 = elementMap patKey patVal1
                patMap2 = elementMap patKey patVal2
                patConcat = concatMap patMap1 patMap2
                predicate = mkEquals_ mkBottom_ patConcat
            (===) OrPattern.bottom =<< evaluateT patConcat
            (===) OrPattern.top =<< evaluateT predicate
        )

test_concatCommutes :: TestTree
test_concatCommutes =
    testPropertyWithSolver
        "concat{}(as, bs) === concat{}(bs, as)"
        ( do
            patMap1 <- forAll genMapPattern
            patMap2 <- forAll genMapPattern
            let patConcat1 = concatMap patMap1 patMap2
                patConcat2 = concatMap patMap2 patMap1
                predicate = mkEquals_ patConcat1 patConcat2
            actual1 <- evaluateT patConcat1
            actual2 <- evaluateT patConcat2
            (===) actual1 actual2
            (===) OrPattern.top =<< evaluateT predicate
        )

test_concatAssociates :: TestTree
test_concatAssociates =
    testPropertyWithSolver
        "concat{}(concat{}(as, bs), cs) === concat{}(as, concat{}(bs, cs))"
        ( do
            patMap1 <- forAll genMapPattern
            patMap2 <- forAll genMapPattern
            patMap3 <- forAll genMapPattern
            let patConcat12 = concatMap patMap1 patMap2
                patConcat23 = concatMap patMap2 patMap3
                patConcat12_3 = concatMap patConcat12 patMap3
                patConcat1_23 = concatMap patMap1 patConcat23
                predicate = mkEquals_ patConcat12_3 patConcat1_23
            actual12_3 <- evaluateT patConcat12_3
            actual1_23 <- evaluateT patConcat1_23
            (===) actual12_3 actual1_23
            (===) OrPattern.top =<< evaluateT predicate
        )

test_inKeysUnit :: TestTree
test_inKeysUnit =
    testPropertyWithSolver
        "inKeys{}(unit{}(), key) === \\dv{Bool{}}(\"false\")"
        ( do
            patKey <- forAll genIntegerPattern
            let patUnit = unitMap
                patInKeys = inKeysMap patKey patUnit
                predicate = mkEquals_ (Test.Bool.asInternal False) patInKeys
            (===) (Test.Bool.asOrPattern False) =<< evaluateT patInKeys
            (===) OrPattern.top =<< evaluateT predicate
        )

test_keysUnit :: TestTree
test_keysUnit =
    testCaseWithoutSMT
        "keys{}(unit{}() : Map{}) === unit{}() : Set{}"
        $ do
            let patUnit = unitMap
                patKeys = keysMap patUnit
                patExpect = mkSet_ HashSet.empty
                predicate = mkEquals_ patExpect patKeys
            expect <- evaluate patExpect
            assertEqual "" expect =<< evaluate patKeys
            assertEqual "" OrPattern.top =<< evaluate predicate

test_keysElement :: TestTree
test_keysElement =
    testPropertyWithSolver
        "keys{}(element{}(key, _) : Map{}) === element{}(key) : Set{}"
        ( do
            key <- forAll genIntegerKey
            val <- forAll genIntegerPattern
            let patMap = asTermLike $ HashMap.singleton key val
                patKeys = mkSet_ (HashSet.singleton $ from key) & fromConcrete
                patSymbolic = keysMap patMap
                predicate = mkEquals_ patKeys patSymbolic
            expect <- evaluateT patKeys
            (===) expect =<< evaluateT patSymbolic
            (===) OrPattern.top =<< evaluateT predicate
        )

test_keys :: TestTree
test_keys =
    testPropertyWithSolver
        "MAP.keys"
        ( do
            map1 <- forAll (genConcreteMap genIntegerPattern)
            let keys1 = HashMap.keysSet map1 & HashSet.map from
                patConcreteKeys = mkSet_ keys1 & fromConcrete
                patMap = asTermLike map1
                patSymbolicKeys = keysMap patMap
                predicate = mkEquals_ patConcreteKeys patSymbolicKeys
            expect <- evaluateT patConcreteKeys
            (===) expect =<< evaluateT patSymbolicKeys
            (===) OrPattern.top =<< evaluateT predicate
        )

test_keysListUnit :: TestTree
test_keysListUnit =
    testCaseWithoutSMT
        "keys_list{}(unit{}() : Map{}) === unit{}() : List{}"
        $ do
            let patUnit = unitMap
                patKeys = keysListMap patUnit
                patExpect = Test.List.asTermLike []
                predicate = mkEquals_ patExpect patKeys
            expect <- evaluate patExpect
            assertEqual "" expect =<< evaluate patKeys
            assertEqual "" OrPattern.top =<< evaluate predicate

test_keysListElement :: TestTree
test_keysListElement =
    testPropertyWithSolver
        "keys_list{}(element{}(key, _) : Map{}) === element{}(key) : List{}"
        ( do
            key <- forAll genIntegerKey
            val <- forAll genIntegerPattern
            let patMap = asTermLike $ HashMap.singleton key val
                patKeys = Test.List.asTermLike [from key]
                patSymbolic = keysListMap patMap
                predicate = mkEquals_ patKeys patSymbolic
            expect <- evaluateT patKeys
            (===) expect =<< evaluateT patSymbolic
            (===) OrPattern.top =<< evaluateT predicate
        )

test_keysList :: TestTree
test_keysList =
    testPropertyWithSolver
        "MAP.keys_list"
        ( do
            map1 <- forAll (genConcreteMap genIntegerPattern)
            let keys1 = from <$> HashMap.keys map1
                patConcreteKeys = Test.List.asTermLike keys1
                patMap = asTermLike map1
                patSymbolicKeys = keysListMap patMap
                predicate = mkEquals_ patConcreteKeys patSymbolicKeys
            expect <- evaluateT patConcreteKeys
            (===) expect =<< evaluateT patSymbolicKeys
            (===) OrPattern.top =<< evaluateT predicate
        )

test_inKeysElement :: TestTree
test_inKeysElement =
    testPropertyWithSolver
        "inKeys{}(element{}(key, _), key) === \\dv{Bool{}}(\"true\")"
        ( do
            patKey <- forAll genIntegerPattern
            patVal <- forAll genIntegerPattern
            let patMap = elementMap patKey patVal
                patInKeys = inKeysMap patKey patMap
                predicate = mkEquals_ (Test.Bool.asInternal True) patInKeys
            (===) (Test.Bool.asOrPattern True) =<< evaluateT patInKeys
            (===) OrPattern.top =<< evaluateT predicate
        )

test_values :: TestTree
test_values =
    testPropertyWithSolver
        "MAP.values"
        ( do
            map1 <- forAll (genConcreteMap genIntegerPattern)
            let values = HashMap.elems map1
                patConcreteValues =
                    Test.List.asTermLike $ builtinList values
                patMap = asTermLike map1
                patValues = valuesMap patMap
                predicate = mkEquals_ patConcreteValues patValues
            expect <- evaluateT patValues
            (===) expect =<< evaluateT patConcreteValues
            (===) OrPattern.top =<< evaluateT predicate
        )

test_inclusion :: [TestTree]
test_inclusion =
    [ testPropertyWithSolver
        "MAP.inclusion success"
        ( do
            patKey1 <- forAll genIntegerPattern
            patKey2 <- forAll genIntegerPattern
            when (patKey1 == patKey2) discard
            patVal1 <- forAll genIntegerPattern
            patVal2 <- forAll genIntegerPattern
            let patMap1 = elementMap patKey1 patVal1
                patMap2 = concatMap patMap1 (elementMap patKey2 patVal2)
                patInclusion = inclusionMap patMap1 patMap2
                predicate =
                    mkImplies
                        (mkNot (mkEquals_ patKey1 patKey2))
                        (mkEquals_ (Test.Bool.asInternal True) patInclusion)
            (===) (Test.Bool.asOrPattern True) =<< evaluateT patInclusion
            (===) OrPattern.top =<< evaluateT predicate
        )
    , testPropertyWithSolver
        "MAP.inclusion success: empty map <= empty map"
        ( do
            let patInclusion = inclusionMap unitMap unitMap
                predicate = mkEquals_ (Test.Bool.asInternal True) patInclusion
            (===) (Test.Bool.asOrPattern True) =<< evaluateT patInclusion
            (===) OrPattern.top =<< evaluateT predicate
        )
    , testPropertyWithSolver
        "MAP.inclusion success: empty map <= any map"
        ( do
            patSomeMap <- forAll genMapPattern
            let patInclusion = inclusionMap unitMap patSomeMap
                predicate = mkEquals_ (Test.Bool.asInternal True) patInclusion
            (===) (Test.Bool.asOrPattern True) =<< evaluateT patInclusion
            (===) OrPattern.top =<< evaluateT predicate
        )
    , testPropertyWithSolver
        "MAP.inclusion failure: !(some map <= empty map)"
        ( do
            patKey1 <- forAll genIntegerPattern
            patVal1 <- forAll genIntegerPattern
            let patSomeMap = elementMap patKey1 patVal1
                patInclusion = inclusionMap patSomeMap unitMap
                predicate = mkEquals_ (Test.Bool.asInternal False) patInclusion
            (===) (Test.Bool.asOrPattern False) =<< evaluateT patInclusion
            (===) OrPattern.top =<< evaluateT predicate
        )
    , testPropertyWithSolver
        "MAP.inclusion failure: lhs key not included in rhs map"
        ( do
            patKey1 <- forAll genIntegerPattern
            patKey2 <- forAll genIntegerPattern
            when (patKey1 == patKey2) discard
            patVal1 <- forAll genIntegerPattern
            patVal2 <- forAll genIntegerPattern
            let patMap1 = elementMap patKey1 patVal1
                patMap2 = concatMap patMap1 (elementMap patKey2 patVal2)
                patInclusion = inclusionMap patMap2 patMap1
                predicate =
                    mkImplies
                        (mkNot (mkEquals_ patKey1 patKey2))
                        (mkEquals_ (Test.Bool.asInternal False) patInclusion)
            (===) (Test.Bool.asOrPattern False) =<< evaluateT patInclusion
            (===) OrPattern.top =<< evaluateT predicate
        )
    , testPropertyWithSolver
        "MAP.inclusion failure: lhs key maps differently in rhs map"
        ( do
            patKey1 <- forAll genIntegerPattern
            patKey2 <- forAll genIntegerPattern
            patVal1 <- forAll genIntegerPattern
            patVal1' <- forAll genIntegerPattern
            patVal2 <- forAll genIntegerPattern

            when (patKey1 == patKey2) discard
            when (patVal1 == patVal1') discard

            let patMap1 = elementMap patKey1 patVal1
                patMap2 = concatMap (elementMap patKey1 patVal1') (elementMap patKey2 patVal2)
                patInclusion = inclusionMap patMap1 patMap2
                predicate =
                    mkImplies
                        (mkNot (mkEquals_ patKey1 patKey2))
                        (mkEquals_ (Test.Bool.asInternal False) patInclusion)
            (===) (Test.Bool.asOrPattern False) =<< evaluateT patInclusion
            (===) OrPattern.top =<< evaluateT predicate
        )
    ]

-- | Check that simplification is carried out on map elements.
test_simplify :: TestTree
test_simplify =
    testCaseWithoutSMT "simplify builtin Map elements" $ do
        let x = mkIntConfigVar (testId "x")
            key = Test.Int.asKey 1
            original = asTermLike $ HashMap.fromList [(key, mkAnd x mkTop_)]
            expected =
                MultiOr.singleton . asPattern $ HashMap.fromList [(key, x)]
        actual <- evaluate original
        assertEqual "expected simplified Map" expected actual

-- | Maps with symbolic keys are not simplified.
test_symbolic :: TestTree
test_symbolic =
    testPropertyWithSolver
        "builtin functions are evaluated on symbolic keys"
        ( do
            elements <- forAll $ genMapSortedVariable intSort genIntegerPattern
            let varMap = mapKeys mkElemVar elements
                patMap = asSymbolicPattern varMap
                expect = MultiOr.singleton $ asVariablePattern varMap
            if HashMap.null elements
                then discard
                else (===) expect =<< evaluateT patMap
        )

test_isBuiltin :: [TestTree]
test_isBuiltin =
    [ testCase "isSymbolConcat" $ do
        assertBool "" (Map.isSymbolConcat Mock.concatMapSymbol)
        assertBool "" (not (Map.isSymbolConcat Mock.aSymbol))
        assertBool "" (not (Map.isSymbolConcat Mock.elementMapSymbol))
    , testCase "isSymbolElement" $ do
        assertBool "" (Map.isSymbolElement Mock.elementMapSymbol)
        assertBool "" (not (Map.isSymbolElement Mock.aSymbol))
        assertBool "" (not (Map.isSymbolElement Mock.concatMapSymbol))
    , testCase "isSymbolUnit" $ do
        assertBool "" (Map.isSymbolUnit Mock.unitMapSymbol)
        assertBool "" (not (Map.isSymbolUnit Mock.aSymbol))
        assertBool "" (not (Map.isSymbolUnit Mock.concatMapSymbol))
    ]

-- | Unify two maps with concrete keys and variable values.
test_unifyConcrete :: TestTree
test_unifyConcrete =
    testPropertyWithSolver
        "unify maps with concrete keys and symbolic values"
        ( do
            let genVariablePair =
                    (,) <$> genIntVariable <*> genIntVariable
                  where
                    genIntVariable =
                        standaloneGen $
                            mkElemVar <$> configElementVariableGen intSort
            map12 <- forAll (genConcreteMap genVariablePair)
            let map1 = fst <$> map12
                map2 = snd <$> map12
                patExpect =
                    asTermLike (uncurry mkAnd <$> map12)
                patActual =
                    mkAnd (asTermLike map1) (asTermLike map2)
                predicate = mkEquals_ patExpect patActual
            expect <- evaluateT patExpect
            actual <- evaluateT patActual
            (===) expect actual
            (===) OrPattern.top =<< evaluateT predicate
        )

-- Given a function to scramble the arguments to concat, i.e.,
-- @id@ or @reverse@, produces a pattern of the form
-- `MapItem(absInt(K:Int), absInt(V:Int)) Rest:Map`, or
-- `Rest:Map MapItem(absInt(K:Int), absInt(V:Int))`, respectively.
selectFunctionPattern ::
    -- |key variable
    ElementVariable RewritingVariableName ->
    -- |value variable
    ElementVariable RewritingVariableName ->
    -- |map variable
    ElementVariable RewritingVariableName ->
    -- |scrambling function
    (forall a. [a] -> [a]) ->
    TermLike RewritingVariableName
selectFunctionPattern keyVar valueVar mapVar permutation =
    mkApplySymbol concatMapSymbol $ permutation [singleton, mkElemVar mapVar]
  where
    key = mkApplySymbol absIntSymbol [mkElemVar keyVar]
    value = mkApplySymbol absIntSymbol [mkElemVar valueVar]
    singleton = mkApplySymbol elementMapSymbol [key, value]

makeElementSelect ::
    ElementVariable RewritingVariableName ->
    ElementVariable RewritingVariableName ->
    TermLike RewritingVariableName
makeElementSelect keyVar valueVar =
    mkApplySymbol elementMapSymbol [mkElemVar keyVar, mkElemVar valueVar]

makeElementLookup ::
    TermLike Concrete ->
    ElementVariable RewritingVariableName ->
    TermLike RewritingVariableName
makeElementLookup key valueVar =
    mkApplySymbol
        elementMapSymbol
        [TermLike.fromConcrete key, mkElemVar valueVar]

-- Given a function to scramble the arguments to concat, i.e.,
-- @id@ or @reverse@, produces a pattern of the form
-- `MapItem(K:Int, V:Int) Rest:Map`, or `Rest:Map MapItem(K:Int, V:Int)`,
-- respectively.
selectPattern ::
    -- |key variable
    ElementVariable RewritingVariableName ->
    -- |value variable
    ElementVariable RewritingVariableName ->
    -- |map variable
    ElementVariable RewritingVariableName ->
    -- |scrambling function
    (forall a. [a] -> [a]) ->
    TermLike RewritingVariableName
selectPattern keyVar valueVar mapVar permutation =
    mkApplySymbol concatMapSymbol $ permutation [element, mkElemVar mapVar]
  where
    element = makeElementSelect keyVar valueVar

addSelectElement ::
    -- |key variable
    ElementVariable RewritingVariableName ->
    -- |value variable
    ElementVariable RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
addSelectElement keyVar valueVar mapPattern =
    mkApplySymbol concatMapSymbol [element, mapPattern]
  where
    element = makeElementSelect keyVar valueVar

addLookupElement ::
    -- |key
    TermLike Concrete ->
    -- |value variable
    ElementVariable RewritingVariableName ->
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName
addLookupElement key valueVar mapPattern =
    mkApplySymbol concatMapSymbol [element, mapPattern]
  where
    element = makeElementLookup key valueVar

test_unifyEmptyWithEmpty :: TestTree
test_unifyEmptyWithEmpty =
    testPropertyWithoutSolver "Unify empty map pattern with empty map DV" $ do
        -- Map.empty /\ mapUnit
        (emptyMapDV `unifiesWithMulti` emptyMapPattern) [expect]
        -- mapUnit /\ Map.empty
        (emptyMapPattern `unifiesWithMulti` emptyMapDV) [expect]
  where
    emptyMapDV :: TermLike RewritingVariableName
    emptyMapDV = asInternal []
    emptyMapPattern = asTermLike HashMap.empty
    expect =
        Conditional
            { term = emptyMapDV
            , predicate = makeTruePredicate
            , substitution = Substitution.unsafeWrap []
            }

test_unifySelectFromEmpty :: TestTree
test_unifySelectFromEmpty =
    testPropertyWithSolver "unify an empty map with a selection pattern" $ do
        keyVar <- forAll (standaloneGen $ configElementVariableGen intSort)
        valueVar <- forAll (standaloneGen $ configElementVariableGen intSort)
        mapVar <- forAll (standaloneGen $ configElementVariableGen mapSort)
        let variables = [keyVar, valueVar, mapVar]
        unless (distinctVariables variables) discard
        let selectPat = selectPattern keyVar valueVar mapVar id
            selectPatRev = selectPattern keyVar valueVar mapVar reverse
            fnSelectPat = selectFunctionPattern keyVar valueVar mapVar id
            fnSelectPatRev =
                selectFunctionPattern keyVar valueVar mapVar reverse
        -- Map.empty /\ MapItem(K:Int, V:Int) Rest:Map
        emptyMap `doesNotUnifyWith` selectPat
        selectPat `doesNotUnifyWith` emptyMap
        -- Map.empty /\ Rest:Map MapItem(K:Int, V:int)
        emptyMap `doesNotUnifyWith` selectPatRev
        selectPatRev `doesNotUnifyWith` emptyMap
        -- Map.empty /\ MapItem(absInt(K:Int), absInt(V:Int)) Rest:Map
        emptyMap `doesNotUnifyWith` fnSelectPat
        fnSelectPat `doesNotUnifyWith` emptyMap
        -- Map.empty /\ Rest:Map MapItem(absInt(K:Int), absInt(V:Int))
        emptyMap `doesNotUnifyWith` fnSelectPatRev
        fnSelectPatRev `doesNotUnifyWith` emptyMap
  where
    emptyMap = asTermLike HashMap.empty
    doesNotUnifyWith pat1 pat2 =
        (===) OrPattern.bottom =<< evaluateT (mkAnd pat1 pat2)

test_unifySelectFromSingleton :: TestTree
test_unifySelectFromSingleton =
    testPropertyWithoutSolver
        "unify a singleton map with a variable selection pattern"
        ( do
            key <- forAll genIntegerPattern
            value <- forAll genIntegerPattern
            keyVar <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            valueVar <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            mapVar <-
                forAll (standaloneGen $ configElementVariableGen mapSort)
            let variables = [keyVar, valueVar, mapVar]
            unless (distinctVariables variables) discard
            let selectPat = selectPattern keyVar valueVar mapVar id
                selectPatRev = selectPattern keyVar valueVar mapVar reverse
                singleton = asInternal [(key, value)]
                expect =
                    Conditional
                        { term = singleton
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject mapVar, asInternal [])
                                , (inject keyVar, key)
                                , (inject valueVar, value)
                                ]
                        }
            -- { 5 -> 7 } /\ Item(K:Int, V:Int) Rest:Map
            (singleton `unifiesWith` selectPat) expect
            (selectPat `unifiesWith` singleton) expect
            -- { 5 -> 7 } /\ Rest:Map MapItem(K:Int, V:Int)
            (singleton `unifiesWith` selectPatRev) expect
            (selectPatRev `unifiesWith` singleton) expect
        )

test_unifySelectSingletonFromSingleton :: TestTree
test_unifySelectSingletonFromSingleton =
    testPropertyWithoutSolver
        "unify a singleton map with a singleton variable selection pattern"
        ( do
            key <- forAll genIntegerPattern
            value <- forAll genIntegerPattern
            keyVar <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            valueVar <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let variables = [keyVar, valueVar]
            unless (distinctVariables variables) discard
            let emptyMapPat = asTermLike HashMap.empty
                selectPat = addSelectElement keyVar valueVar emptyMapPat
                singleton = asInternal [(key, value)]
                expect =
                    Conditional
                        { term = singleton
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject keyVar, key)
                                , (inject valueVar, value)
                                ]
                        }
            -- { 5 -> 7 } /\ Item(K:Int, V:Int) Map.unit
            (singleton `unifiesWith` selectPat) expect
            (selectPat `unifiesWith` singleton) expect
        )

test_unifySelectFromSingletonWithoutLeftovers :: TestTree
test_unifySelectFromSingletonWithoutLeftovers =
    testPropertyWithoutSolver
        "unify a singleton map with an element selection pattern"
        ( do
            key <- forAll genIntegerPattern
            value <- forAll genIntegerPattern
            keyVar <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            valueVar <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            let variables = [keyVar, valueVar]
            unless (distinctVariables variables) discard
            let selectPat = makeElementSelect keyVar valueVar
                singleton = asInternal [(key, value)]
                expect =
                    Conditional
                        { term = singleton
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject keyVar, key)
                                , (inject valueVar, value)
                                ]
                        }
            -- { 5 -> 7 } /\ Item(K:Int, V:Int)
            (singleton `unifiesWith` selectPat) expect
            (selectPat `unifiesWith` singleton) expect
        )

test_unifySelectFromTwoElementMap :: TestTree
test_unifySelectFromTwoElementMap =
    testPropertyWithoutSolver
        "unify a two element map with a variable selection pattern"
        ( do
            key1 <- forAll genIntegerPattern
            value1 <- forAll genIntegerPattern
            key2 <- forAll genIntegerPattern
            value2 <- forAll genIntegerPattern
            when (key1 == key2) discard

            keyVar <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            valueVar <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            mapVar <-
                forAll (standaloneGen $ configElementVariableGen mapSort)
            let variables = [keyVar, valueVar, mapVar]
            unless (distinctVariables variables) discard

            let selectPat = selectPattern keyVar valueVar mapVar id
                selectPatRev = selectPattern keyVar valueVar mapVar reverse
                mapDV = asInternal [(key1, value1), (key2, value2)]
                expect1 =
                    Conditional
                        { term = mapDV
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject mapVar, asInternal [(key2, value2)])
                                , (inject keyVar, key1)
                                , (inject valueVar, value1)
                                ]
                        }
                expect2 =
                    Conditional
                        { term = mapDV
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject mapVar, asInternal [(key1, value1)])
                                , (inject keyVar, key2)
                                , (inject valueVar, value2)
                                ]
                        }
            -- { 5 -> 6, 7 -> 8 } /\ Item(K:Int, V:Int) Rest:Map
            (mapDV `unifiesWithMulti` selectPat) [expect1, expect2]
            (selectPat `unifiesWithMulti` mapDV) [expect1, expect2]
            -- { 5 -> 6, 7 -> 8 } /\ Rest:Map Item(K:Int, V:Int)
            (mapDV `unifiesWithMulti` selectPatRev) [expect1, expect2]
            (selectPatRev `unifiesWithMulti` mapDV) [expect1, expect2]
        )

test_unifySelectTwoFromTwoElementMap :: TestTree
test_unifySelectTwoFromTwoElementMap =
    testPropertyWithoutSolver
        "unify a two element map with a binary variable selection pattern"
        ( do
            key1 <- forAll genIntegerPattern
            value1 <- forAll genIntegerPattern
            key2 <- forAll genIntegerPattern
            value2 <- forAll genIntegerPattern
            when (key1 == key2) discard

            keyVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            valueVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            keyVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            valueVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            mapVar <-
                forAll (standaloneGen $ configElementVariableGen mapSort)
            let variables = [keyVar1, keyVar2, valueVar1, valueVar2, mapVar]
            unless (distinctVariables variables) discard

            let selectPat =
                    addSelectElement keyVar1 valueVar1 $
                        addSelectElement keyVar2 valueVar2 $
                            mkElemVar mapVar
                mapDV = asInternal [(key1, value1), (key2, value2)]
                expect1 =
                    Conditional
                        { term = mapDV
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject mapVar, asInternal [])
                                , (inject keyVar1, key1)
                                , (inject keyVar2, key2)
                                , (inject valueVar1, value1)
                                , (inject valueVar2, value2)
                                ]
                        }
                expect2 =
                    Conditional
                        { term = mapDV
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject mapVar, asInternal [])
                                , (inject keyVar1, key2)
                                , (inject keyVar2, key1)
                                , (inject valueVar1, value2)
                                , (inject valueVar2, value1)
                                ]
                        }

            -- { 5 } /\ MapItem(X:Int) Rest:Map
            (mapDV `unifiesWithMulti` selectPat) [expect1, expect2]
            (selectPat `unifiesWithMulti` mapDV) [expect1, expect2]
        )

test_unifySameSymbolicKey :: TestTree
test_unifySameSymbolicKey =
    testPropertyWithoutSolver
        "unify a single element symbolic map with a symbolic selection pattern"
        ( do
            value1 <- forAll genIntegerPattern
            keyVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            valueVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            mapVar <-
                forAll (standaloneGen $ configElementVariableGen mapSort)
            let variables = [keyVar1, valueVar1, mapVar]
            unless (distinctVariables variables) discard

            let selectPat =
                    addSelectElement keyVar1 valueVar1 $
                        mkElemVar mapVar
                mapValue =
                    asVariableInternal
                        (HashMap.singleton (mkElemVar keyVar1) value1)
                expect1 =
                    Conditional
                        { term = mapValue
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject mapVar, asInternal [])
                                , (inject valueVar1, value1)
                                ]
                        }

            -- { x -> 5 } /\ MapItem(x:Int, y:Int) Rest:Map
            (mapValue `unifiesWithMulti` selectPat) [expect1]
            (selectPat `unifiesWithMulti` mapValue) [expect1]
        )

test_unifySameSymbolicKeySymbolicOpaque :: TestTree
test_unifySameSymbolicKeySymbolicOpaque =
    testPropertyWithoutSolver
        "unify two symbolic maps with identical keys and one variable opaque"
        ( do
            key1 <- forAll genIntegerKey
            value1 <- forAll genIntegerPattern
            value2 <- forAll genIntegerPattern

            keyVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            valueVar1 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            valueVar2 <-
                forAll (standaloneGen $ configElementVariableGen intSort)
            mapVar1 <-
                forAll (standaloneGen $ configElementVariableGen mapSort)
            mapVar2 <-
                forAll (standaloneGen $ configElementVariableGen mapSort)
            let variables = [keyVar2, valueVar1, valueVar2, mapVar1, mapVar2]
            unless (distinctVariables variables) discard

            let (minMapVar, maxMapVar) =
                    if mapVar1 < mapVar2
                        then (mapVar1, mapVar2)
                        else (mapVar2, mapVar1)
                selectPat =
                    addLookupElement (from key1) valueVar1 $
                        addSelectElement keyVar2 valueVar2 $
                            mkElemVar mapVar2
                mapValueFromVar mapVar =
                    Ac.asInternal testMetadataTools mapSort $
                        wrapAc
                            NormalizedAc
                                { elementsWithVariables =
                                    [MapElement (mkElemVar keyVar2, value2)]
                                , concreteElements =
                                    HashMap.singleton key1 (MapValue value1)
                                , opaque = [mkElemVar mapVar]
                                }
                mapValue = mapValueFromVar mapVar1
                unifiedMap = mapValueFromVar maxMapVar
                expect1 =
                    Conditional
                        { term = unifiedMap
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (inject minMapVar, mkElemVar maxMapVar)
                                , (inject valueVar1, value1)
                                , (inject valueVar2, value2)
                                ]
                        }

            -- { x -> 5 } /\ MapItem(x:Int, y:Int) Rest:Map
            (mapValue `unifiesWithMulti` selectPat) [expect1]
            (selectPat `unifiesWithMulti` mapValue) [expect1]
        )

-- use as (pat1 `unifiesWith` pat2) expect
unifiesWith ::
    HasCallStack =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    Pattern RewritingVariableName ->
    PropertyT NoSMT ()
unifiesWith pat1 pat2 expected =
    unifiesWithMulti pat1 pat2 [expected]

-- use as (pat1 `unifiesWithMulti` pat2) expect
unifiesWithMulti ::
    HasCallStack =>
    TermLike RewritingVariableName ->
    TermLike RewritingVariableName ->
    [Pattern RewritingVariableName] ->
    PropertyT NoSMT ()
unifiesWithMulti pat1 pat2 expectedResults = do
    actualResults <- lift $ evaluateToList (mkAnd pat1 pat2)
    compareElements (List.sort expectedResults) actualResults
  where
    compareElements [] actuals = [] === actuals
    compareElements expecteds [] = expecteds === []
    compareElements (expected : expecteds) (actual : actuals) = do
        compareElement expected actual
        compareElements expecteds actuals
    compareElement
        Conditional
            { term = expectedTerm
            , predicate = expectedPredicate
            , substitution = expectedSubstitution
            }
        Conditional
            { term = actualTerm
            , predicate = actualPredicate
            , substitution = actualSubstitution
            } =
            do
                Substitution.toMap expectedSubstitution
                    === Substitution.toMap actualSubstitution
                expectedPredicate === actualPredicate
                expectedTerm === actualTerm

{- | Unify a concrete map with symbolic-keyed map.

@
(1, 1 |-> 2) ∧ (x, x |-> v)
@

Iterated unification must turn the symbolic key @x@ into a concrete key by
unifying the first element of the pair. This also requires that Map unification
return a partial result for unifying the second element of the pair.
-}
test_concretizeKeys :: TestTree
test_concretizeKeys =
    testCaseWithoutSMT
        "unify a concrete Map with a symbolic Map"
        $ do
            actual <- evaluate original
            assertEqual "expected simplified Map" expected actual
  where
    x =
        mkElementVariable (testId "x") intSort
            & mapElementVariable (pure mkConfigVariable)
    v =
        mkElementVariable (testId "v") intSort
            & mapElementVariable (pure mkConfigVariable)
    key :: TermLike RewritingVariableName
    key = fromConcrete $ Test.Int.asInternal 1
    val = Test.Int.asInternal 2
    concreteMap = asInternal [(key, val)]
    symbolic = asSymbolicPattern $ HashMap.fromList [(mkElemVar x, mkElemVar v)]
    original =
        mkAnd
            (mkPair intSort mapSort (Test.Int.asInternal 1) concreteMap)
            (mkPair intSort mapSort (mkElemVar x) symbolic)
    expected =
        Conditional
            { term = mkPair intSort mapSort key (asInternal [(key, val)])
            , predicate = Predicate.makeTruePredicate
            , substitution =
                Substitution.unsafeWrap [(inject v, val), (inject x, key)]
            }
            & MultiOr.singleton

{- | Unify a concrete map with symbolic-keyed map in an axiom

Apply the axiom
@
(x, x |-> v) => v
@
to the configuration
@
(1, 1 |-> 2)
@
yielding @2@.

Iterated unification must turn the symbolic key @x@ into a concrete key by
unifying the first element of the pair. This also requires that Map unification
return a partial result for unifying the second element of the pair.
-}
test_concretizeKeysAxiom :: TestTree
test_concretizeKeysAxiom =
    testCaseWithoutSMT
        "unify a concrete Map with a symbolic Map in an axiom"
        $ do
            let concreteMap = asTermLike $ HashMap.fromList [(key, val)]
            config <- evaluate $ pair symbolicKey concreteMap
            actual <- MultiOr.traverse (flip runStep axiom) config
            assertEqual "expected MAP.lookup" expected (MultiOr.flatten actual)
  where
    x = mkIntRuleVar (testId "x")
    v = mkIntRuleVar (testId "v")
    key = Test.Int.asKey 1
    symbolicKey = from key
    val = Test.Int.asInternal 2
    symbolicMap = asSymbolicPattern $ HashMap.fromList [(x, v)]
    axiom =
        RewriteRule
            RulePattern
                { left = mkPair intSort mapSort x symbolicMap
                , antiLeft = Nothing
                , requires = Predicate.makeTruePredicate
                , rhs = injectTermIntoRHS v
                , attributes = Default.def
                }
    expected =
        MultiOr.make
            [ Conditional
                { term = val
                , predicate = makeTruePredicate
                , substitution = mempty
                }
            ]

test_renormalize :: [TestTree]
test_renormalize =
    [ unchanged "abstract key is unchanged" (mkMap' [(x, v)] [] [])
    , becomes
        "concrete key is normalized"
        (mkMap' [(from k1, v)] [] [])
        (mkMap' [] [(k1, v)] [])
    , becomes
        "opaque child is flattened"
        (mkMap' [] [(k1, v)] [mkMap' [] [(k2, v)] []])
        (mkMap' [] [(k1, v), (k2, v)] [])
    , becomes
        "child is flattened and normalized"
        (mkMap' [] [(k1, v)] [mkMap' [(from k2, v)] [] []])
        (mkMap' [] [(k1, v), (k2, v)] [])
    , becomes
        "grandchild is flattened and normalized"
        (mkMap' [] [(k1, v)] [mkMap' [(x, v)] [] [mkMap' [(from k2, v)] [] []]])
        (mkMap' [(x, v)] [(k1, v), (k2, v)] [])
    , denorm
        "duplicate key in map"
        (mkMap' [(from k1, v), (from k1, v)] [] [])
    , denorm
        "duplicate key in child"
        (mkMap' [(from k1, v)] [] [mkMap' [(from k1, v)] [] []])
    ]
  where
    x = mkIntConfigVar (testId "x")
    v = mkIntConfigVar (testId "v")

    k1, k2 :: Key
    k1 = Test.Int.asKey 1
    k2 = Test.Int.asKey 2

    becomes ::
        HasCallStack =>
        TestName ->
        -- | original, (possibly) de-normalized map
        NormalizedMap Key (TermLike RewritingVariableName) ->
        -- | expected normalized map
        NormalizedMap Key (TermLike RewritingVariableName) ->
        TestTree
    becomes name origin expect =
        testCase name $ assertEqual "" (Just expect) (Ac.renormalize origin)

    unchanged ::
        HasCallStack =>
        TestName ->
        NormalizedMap Key (TermLike RewritingVariableName) ->
        TestTree
    unchanged name origin = becomes name origin origin

    denorm ::
        HasCallStack =>
        TestName ->
        NormalizedMap Key (TermLike RewritingVariableName) ->
        TestTree
    denorm name origin =
        testCase name $ assertEqual "" Nothing (Ac.renormalize origin)

    mkMap' ::
        -- | abstract elements
        [(TermLike RewritingVariableName, TermLike RewritingVariableName)] ->
        -- | concrete elements
        [(Key, TermLike RewritingVariableName)] ->
        -- | opaque terms
        [NormalizedMap Key (TermLike RewritingVariableName)] ->
        NormalizedMap Key (TermLike RewritingVariableName)
    mkMap' abstract concrete opaque =
        wrapAc
            NormalizedAc
                { elementsWithVariables = MapElement <$> abstract
                , concreteElements =
                    HashMap.fromList (Bifunctor.second MapValue <$> concrete)
                , opaque =
                    Ac.asInternal testMetadataTools mapSort <$> opaque
                }

hprop_unparse :: Property
hprop_unparse =
    hpropUnparse
        ( asInternal
            . HashMap.toList
            . mapKeys from
            <$> genConcreteMap genValue
        )
  where
    genValue = Test.Int.asInternal <$> genInteger

test_inKeys :: [TestTree]
test_inKeys =
    [ testCase "empty Map contains no keys" $ do
        actual1 <- inKeys concreteKey (asInternal [])
        assertEqual "no concrete keys" (Just False) actual1
        actual2 <- inKeys x (asInternal [])
        assertEqual "no symbolic keys" (Just False) actual2
        actual3 <- inKeys (tdivInt y z) (asInternal [])
        assertEqual "no partial keys" (Just False) actual3
    , testGroup
        "concrete Map"
        [ testCase "concrete key is present" $ do
            actual <- inKeys concreteKey concreteMap
            assertEqual "" (Just True) actual
        , testCase "concrete key is absent" $ do
            let key = Test.Int.asInternal 2
            actual <- inKeys key concreteMap
            assertEqual "" (Just False) actual
        , testCase "symbolic key is undecided" $ do
            actual <- inKeys x concreteMap
            assertEqual "" Nothing actual
        ]
    , testGroup
        "symbolic Map"
        [ testCase "symbolic key is present" $ do
            actual <- inKeys x symbolicMap
            assertEqual "" (Just True) actual
        , testCase "concrete key is present" $ do
            actual <- inKeys concreteKey symbolicMap
            assertEqual "" (Just True) actual
        , testCase "partial key is present" $ do
            actual <- inKeys (tdivInt y z) symbolicMap
            assertEqual "" (Just True) actual
        , testCase "symbolic key is undecided" $ do
            let key = mkIntConfigVar (testId "z")
            actual <- inKeys key symbolicMap
            assertEqual "" Nothing actual
        , testCase "concrete key is undecided" $ do
            let key = Test.Int.asInternal 2
            actual <- inKeys key symbolicMap
            assertEqual "" Nothing actual
        , testCase "partial key is undecided" $ do
            actual <- inKeys (tdivInt x z) symbolicMap
            assertEqual "" Nothing actual
        ]
    ]
  where
    concreteKey = Test.Int.asInternal 0
    concreteMap =
        asInternal
            [ (Test.Int.asInternal 0, u)
            , (Test.Int.asInternal 1, v)
            ]
    x, y, z, u, v, w :: TermLike RewritingVariableName
    x = mkIntConfigVar (testId "x")
    y = mkIntConfigVar (testId "y")
    z = mkIntConfigVar (testId "z")
    u = mkIntConfigVar (testId "u")
    v = mkIntConfigVar (testId "v")
    w = mkIntConfigVar (testId "w")
    symbolicMap =
        asInternal
            [ (x, u)
            , (tdivInt y z, v)
            , (Test.Int.asInternal 0, w)
            ]
    inKeys ::
        HasCallStack =>
        TermLike RewritingVariableName ->
        TermLike RewritingVariableName ->
        IO (Maybe Bool)
    inKeys termKey termMap = do
        output <-
            Map.evalInKeys
                SideCondition.top
                boolSort
                [termKey, termMap]
                & runMaybeT
                & runSimplifier testEnv
        case output of
            Nothing -> return Nothing
            Just result -> do
                let (term, condition) = splitTerm result
                assertTop (substitution condition)
                let expectPredicate
                        | null predicates = makeTruePredicate
                        | otherwise = makeMultipleAndPredicate predicates
                    predicates =
                        catMaybes
                            [ mkDefinedTerm termKey
                            , mkDefinedTerm termMap
                            ]
                assertEqual "" expectPredicate (predicate condition)
                bool <- expectBool term
                return (Just bool)

    mkDefinedTerm term = do
        (guard . not)
            (SideCondition.isDefined SideCondition.top term)
        pure (makeCeilPredicate term)

-- * Helpers

-- | Construct a pattern for a map which may have symbolic keys.
asSymbolicPattern ::
    HashMap (TermLike RewritingVariableName) (TermLike RewritingVariableName) ->
    TermLike RewritingVariableName
asSymbolicPattern result
    | HashMap.null result =
        applyUnit
    | otherwise =
        foldr1 applyConcat (applyElement <$> HashMap.toList result)
  where
    applyUnit = mkApplySymbol unitMapSymbol []
    applyElement (key, value) = elementMap key value
    applyConcat map1 map2 = concatMap map1 map2

-- | Specialize 'Map.asTermLike' to the builtin sort 'mapSort'.
asTermLike ::
    InternalVariable variable =>
    HashMap Key (TermLike variable) ->
    TermLike variable
asTermLike = asInternal . fmap (Bifunctor.first from) . HashMap.toList

-- | Specialize 'Map.asPattern' to the builtin sort 'mapSort'.
asPattern ::
    HashMap Key (TermLike RewritingVariableName) ->
    Pattern RewritingVariableName
asPattern concreteMap =
    Reflection.give testMetadataTools $
        Ac.asPattern mapSort $
            wrapAc
                NormalizedAc
                    { elementsWithVariables = []
                    , concreteElements = MapValue <$> concreteMap
                    , opaque = []
                    }

asVariablePattern ::
    HashMap (TermLike RewritingVariableName) (TermLike RewritingVariableName) ->
    Pattern RewritingVariableName
asVariablePattern variableMap =
    Reflection.give testMetadataTools $
        Ac.asPattern mapSort $
            wrapAc
                NormalizedAc
                    { elementsWithVariables = MapElement <$> HashMap.toList variableMap
                    , concreteElements = HashMap.empty
                    , opaque = []
                    }

asVariableInternal ::
    HashMap (TermLike RewritingVariableName) (TermLike RewritingVariableName) ->
    TermLike RewritingVariableName
asVariableInternal variableMap =
    Ac.asInternal testMetadataTools mapSort $
        wrapAc
            NormalizedAc
                { elementsWithVariables = MapElement <$> HashMap.toList variableMap
                , concreteElements = HashMap.empty
                , opaque = []
                }

-- | Specialize 'Ac.asInternal' to the builtin sort 'mapSort'.
asInternal ::
    InternalVariable variable =>
    [(TermLike variable, TermLike variable)] ->
    TermLike variable
asInternal elements =
    Ac.asInternal testMetadataTools mapSort $
        wrapAc
            NormalizedAc
                { elementsWithVariables = wrapElement <$> abstractElements
                , concreteElements
                , opaque = []
                }
  where
    asConcrete element@(key, value) =
        (,) <$> retractKey key <*> pure value
            & maybe (Left element) Right
    (abstractElements, HashMap.fromList -> concreteElements) =
        asConcrete . Bifunctor.second MapValue <$> elements
            & partitionEithers

{- | Construct a 'NormalizedMap' from a list of elements and opaque terms.

It is an error if the collection cannot be normalized.
-}
normalizedMap ::
    -- | (abstract or concrete) elements
    [(TermLike RewritingVariableName, TermLike RewritingVariableName)] ->
    -- | opaque terms
    [TermLike RewritingVariableName] ->
    NormalizedMap Key (TermLike RewritingVariableName)
normalizedMap elements opaque =
    Maybe.fromJust . Ac.renormalize . wrapAc $
        NormalizedAc
            { elementsWithVariables = MapElement <$> elements
            , concreteElements = HashMap.empty
            , opaque
            }

-- * Constructors

mkIntRuleVar :: Id -> TermLike RewritingVariableName
mkIntRuleVar variableName =
    mkElemVar $ ruleElementVariableFromId variableName intSort

mkIntConfigVar :: Id -> TermLike RewritingVariableName
mkIntConfigVar variableName =
    mkElemVar $ configElementVariableFromId variableName intSort

asVariableName :: ElementVariable RewritingVariableName -> Id
asVariableName = base . from . unElementVariableName . variableName

distinctVariables :: [ElementVariable RewritingVariableName] -> Bool
distinctVariables variables =
    length variableNames == length (List.nub variableNames)
  where
    variableNames = map asVariableName variables

-- | Utility function for mapping over the keys of a 'HashMap'.
mapKeys ::
    Hashable k2 =>
    Eq k2 =>
    (k1 -> k2) ->
    HashMap k1 v ->
    HashMap k2 v
mapKeys f =
    HashMap.fromList
        . (fmap . Bifunctor.first) f
        . HashMap.toList
