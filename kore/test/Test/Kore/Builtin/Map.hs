module Test.Kore.Builtin.Map where

import Hedgehog
    ( Gen
    , Property
    , PropertyT
    , discard
    , forAll
    , (===)
    )
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty

import qualified Control.Monad as Monad
import qualified Control.Monad.Trans as Trans
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Default as Default
import qualified Data.Either as Either
import Data.Function
    ( (&)
    )
import qualified Data.List as List
import Data.Map
    ( Map
    )
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import qualified Data.Reflection as Reflection
import qualified Data.Set as Set
import qualified GHC.Stack as GHC
import Prelude hiding
    ( concatMap
    )

import Kore.Attribute.Hook
    ( Hook
    )
import qualified Kore.Attribute.Symbol as StepperAttributes
import qualified Kore.Builtin.AssociativeCommutative as Ac
import qualified Kore.Builtin.Map as Map
import qualified Kore.Builtin.Map.Map as Map
import Kore.Domain.Builtin
    ( NormalizedMap (..)
    )
import qualified Kore.Domain.Builtin as Domain
import Kore.IndexedModule.MetadataTools
    ( SmtMetadataTools
    )
import Kore.Internal.MultiOr
    ( MultiOr (..)
    )
import Kore.Internal.Pattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike hiding
    ( asConcrete
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Predicate.Predicate
    ( makeTruePredicate
    )
import qualified Kore.Predicate.Predicate as Predicate
import Kore.Step.Rule
import Kore.Step.Simplification.Simplify
import qualified Kore.Unification.Substitution as Substitution
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable (..)
    )
import SMT
    ( SMT
    )

import Test.Kore
    ( elementVariableGen
    , standaloneGen
    , testId
    )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Kore.Builtin.Int
    ( genConcreteIntegerPattern
    , genInteger
    , genIntegerPattern
    )
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Builtin.Set as Test.Set
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.SMT
import Test.Tasty.HUnit.Ext

genMapInteger :: Gen a -> Gen (Map Integer a)
genMapInteger genElement =
    Gen.map (Range.linear 0 32) ((,) <$> genInteger <*> genElement)

genConcreteMap :: Gen a -> Gen (Map (TermLike Concrete) a)
genConcreteMap genElement =
    Map.mapKeys Test.Int.asInternal <$> genMapInteger genElement

genMapPattern :: Gen (TermLike Variable)
genMapPattern = asTermLike <$> genConcreteMap genIntegerPattern

genMapSortedVariable :: Sort -> Gen a -> Gen (Map (ElementVariable Variable) a)
genMapSortedVariable sort genElement =
    Gen.map
        (Range.linear 0 32)
        ((,) <$> standaloneGen (elementVariableGen sort) <*> genElement)

test_lookupUnit :: TestTree
test_lookupUnit =
    testPropertyWithSolver
        "lookup{}(unit{}(), key) === \\bottom{}()"
        (do
            key <- forAll genIntegerPattern
            let patLookup = lookupMap unitMap key
                predicate = mkEquals_ mkBottom_ patLookup
            (===) Pattern.bottom =<< evaluateT patLookup
            (===) Pattern.top    =<< evaluateT predicate
        )

test_lookupUpdate :: TestTree
test_lookupUpdate =
    testPropertyWithSolver
        "lookup{}(update{}(map, key, val), key) === val"
        (do
            patKey <- forAll genIntegerPattern
            patVal <- forAll genIntegerPattern
            patMap <- forAll genMapPattern
            let patLookup = lookupMap (updateMap patMap patKey patVal) patKey
                predicate = mkEquals_ patLookup patVal
                expect = Pattern.fromTermLike patVal
            (===) expect      =<< evaluateT patLookup
            (===) Pattern.top =<< evaluateT predicate
        )

test_removeUnit :: TestTree
test_removeUnit =
    testPropertyWithSolver
        "remove{}(unit{}(), key) === unit{}()"
        (do
            key <- forAll genIntegerPattern
            let patRemove = removeMap unitMap key
                predicate = mkEquals_ unitMap patRemove
            expect <- evaluateT unitMap
            (===) expect =<< evaluateT patRemove
            (===) Pattern.top =<< evaluateT predicate
        )

test_sizeUnit :: TestTree
test_sizeUnit =
    testPropertyWithSolver
        "MAP.size is size"
        (do
            someMap <- forAll $ genConcreteMap genIntegerPattern
            let
                size = Map.size someMap
                patExpected = Test.Int.asInternal $ toInteger size
                patActual =
                    mkApplySymbol
                        sizeMapSymbol
                        [ asTermLike someMap ]
                predicate = mkEquals_ patExpected patActual
            expect <- evaluateT patExpected
            (===) expect      =<< evaluateT patActual
            (===) Pattern.top =<< evaluateT predicate
        )

test_removeKeyNotIn :: TestTree
test_removeKeyNotIn =
    testPropertyWithSolver
        "MAP.remove key with key not in map"
        (do
            key <- forAll genIntegerPattern
            map' <- forAll genMapPattern
            isInMap <- evaluateT $ lookupMap map' key
            Monad.unless (Pattern.bottom == isInMap) discard
            let patRemove = removeMap map' key
                predicate = mkEquals_ map' patRemove
            expect <- evaluateT map'
            (===) expect =<< evaluateT patRemove
            (===) Pattern.top =<< evaluateT predicate
        )

test_removeKeyIn :: TestTree
test_removeKeyIn =
    testPropertyWithSolver
        "MAP.remove key with key in map"
        (do
            key <- forAll genIntegerPattern
            val <- forAll genIntegerPattern
            map' <- forAll genMapPattern
            isInMap <- evaluateT $ lookupMap map' key
            Monad.unless (Pattern.bottom == isInMap) discard
            let patRemove = removeMap (updateMap map' key val) key
                predicate = mkEquals_ patRemove map'
            expect <- evaluateT map'
            (===) expect =<< evaluateT patRemove
            (===) Pattern.top =<< evaluateT predicate
        )

test_removeAllMapUnit :: TestTree
test_removeAllMapUnit =
    testPropertyWithSolver
        "removeAll{}(unit{}(), set) === unit{}()"
        (do
            set <- forAll Test.Set.genSetPattern
            let patRemoveAll = removeAllMap unitMap set
                predicate = mkEquals_ unitMap patRemoveAll
            expect <- evaluateT unitMap
            (===) expect =<< evaluateT patRemoveAll
            (===) Pattern.top =<< evaluateT predicate
        )

test_removeAllSetUnit :: TestTree
test_removeAllSetUnit =
    testPropertyWithSolver
        "removeAll{}(map, unit{}()) === map"
        (do
            map' <- forAll genMapPattern
            let patRemoveAll = removeAllMap map' unitSet
                predicate = mkEquals_ map' patRemoveAll
            expect <- evaluateT map'
            (===) expect =<< evaluateT patRemoveAll
            (===) Pattern.top =<< evaluateT predicate
        )

test_removeAll :: TestTree
test_removeAll =
    testPropertyWithSolver
        "MAP.removeAll and MAP.remove"
        (do
            map' <- forAll genMapPattern
            set <- forAll Test.Set.genSetConcreteIntegerPattern
            Monad.when (set == Set.empty) discard
            let key = Set.elemAt 0 set
                diffSet = Set.delete key set
                patSet = Test.Set.asTermLike set
                patDiffSet = Test.Set.asTermLike diffSet
                patKey = fromConcrete key
                patRemoveAll1 = removeAllMap map' patSet
                patRemoveAll2 = removeAllMap
                                    (removeMap map' patKey)
                                    patDiffSet
                predicate = mkEquals_ patRemoveAll1 patRemoveAll2
            expect <- evaluateT patRemoveAll2
            (===) expect =<< evaluateT patRemoveAll1
            (===) Pattern.top =<< evaluateT predicate
        )

test_concatUnit :: TestTree
test_concatUnit =
    testPropertyWithSolver
        "concat{}(unit{}(), map) === concat{}(map, unit{}()) === map"
        (do
            patMap <- forAll genMapPattern
            let patConcat2 = concatMap patUnit patMap
                patConcat1 = concatMap patMap patUnit
                patUnit = unitMap
                predicate1 = mkEquals_ patMap patConcat1
                predicate2 = mkEquals_ patMap patConcat2
            expect <- evaluateT patMap
            (===) expect      =<< evaluateT patConcat1
            (===) expect      =<< evaluateT patConcat2
            (===) Pattern.top =<< evaluateT predicate1
            (===) Pattern.top =<< evaluateT predicate2
        )

test_lookupConcatUniqueKeys :: TestTree
test_lookupConcatUniqueKeys =
    testPropertyWithSolver
        "MAP.lookup with two unique keys"
        (do
            patKey1 <- forAll genIntegerPattern
            patKey2 <- forAll genIntegerPattern
            Monad.when (patKey1 == patKey2) discard
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
                        (mkAnd
                            (mkEquals_ patLookup1 patVal1)
                            (mkEquals_ patLookup2 patVal2)
                        )
                expect1 = Pattern.fromTermLike patVal1
                expect2 = Pattern.fromTermLike patVal2
            (===) expect1     =<< evaluateT patLookup1
            (===) expect2     =<< evaluateT patLookup2
            (===) Pattern.top =<< evaluateT predicate
        )

test_concatDuplicateKeys :: TestTree
test_concatDuplicateKeys =
    testPropertyWithSolver
        "concat{}(element{}(key, val1), element{}(key, val2)) === \\bottom{}()"
        (do
            patKey <- forAll genIntegerPattern
            patVal1 <- forAll genIntegerPattern
            patVal2 <- forAll genIntegerPattern
            let patMap1 = elementMap patKey patVal1
                patMap2 = elementMap patKey patVal2
                patConcat = concatMap patMap1 patMap2
                predicate = mkEquals_ mkBottom_ patConcat
            (===) Pattern.bottom =<< evaluateT patConcat
            (===) Pattern.top    =<< evaluateT predicate
        )

test_concatCommutes :: TestTree
test_concatCommutes =
    testPropertyWithSolver
        "concat{}(as, bs) === concat{}(bs, as)"
        (do
            patMap1 <- forAll genMapPattern
            patMap2 <- forAll genMapPattern
            let patConcat1 = concatMap patMap1 patMap2
                patConcat2 = concatMap patMap2 patMap1
                predicate = mkEquals_ patConcat1 patConcat2
            actual1 <- evaluateT patConcat1
            actual2 <- evaluateT patConcat2
            (===) actual1 actual2
            (===) Pattern.top =<< evaluateT predicate
        )

test_concatAssociates :: TestTree
test_concatAssociates =
    testPropertyWithSolver
        "concat{}(concat{}(as, bs), cs) === concat{}(as, concat{}(bs, cs))"
        (do
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
            (===) Pattern.top =<< evaluateT predicate
        )

test_inKeysUnit :: TestTree
test_inKeysUnit =
    testPropertyWithSolver
        "inKeys{}(unit{}(), key) === \\dv{Bool{}}(\"false\")"
        (do
            patKey <- forAll genIntegerPattern
            let patUnit = unitMap
                patInKeys = inKeysMap patKey patUnit
                predicate = mkEquals_ (Test.Bool.asInternal False) patInKeys
            (===) (Test.Bool.asPattern False) =<< evaluateT patInKeys
            (===) Pattern.top                 =<< evaluateT predicate
        )

test_keysUnit :: TestTree
test_keysUnit =
    testCaseWithSMT
        "keys{}(unit{}() : Map{}) === unit{}() : Set{}"
        $ do
            let
                patUnit = unitMap
                patKeys = keysMap patUnit
                patExpect = Test.Set.asTermLike Set.empty
                predicate = mkEquals_ patExpect patKeys
            expect <- evaluate patExpect
            assertEqual "" expect =<< evaluate patKeys
            assertEqual "" Pattern.top =<< evaluate predicate

test_keysElement :: TestTree
test_keysElement =
    testPropertyWithSolver
        "keys{}(element{}(key, _) : Map{}) === element{}(key) : Set{}"
        (do
            key <- forAll genConcreteIntegerPattern
            val <- forAll genIntegerPattern
            let patMap = asTermLike $ Map.singleton key val
                patKeys = Test.Set.asTermLike $ Set.singleton key
                patSymbolic = keysMap patMap
                predicate = mkEquals_ patKeys patSymbolic
            expect <- evaluateT patKeys
            (===) expect      =<< evaluateT patSymbolic
            (===) Pattern.top =<< evaluateT predicate
        )

test_keys :: TestTree
test_keys =
    testPropertyWithSolver
        "MAP.keys"
        (do
            map1 <- forAll (genConcreteMap genIntegerPattern)
            let keys1 = Map.keysSet map1
                patConcreteKeys = Test.Set.asTermLike keys1
                patMap = asTermLike map1
                patSymbolicKeys = keysMap patMap
                predicate = mkEquals_ patConcreteKeys patSymbolicKeys
            expect <- evaluateT patConcreteKeys
            (===) expect      =<< evaluateT patSymbolicKeys
            (===) Pattern.top =<< evaluateT predicate
        )

test_inKeysElement :: TestTree
test_inKeysElement =
    testPropertyWithSolver
        "inKeys{}(element{}(key, _), key) === \\dv{Bool{}}(\"true\")"
        (do
            patKey <- forAll genIntegerPattern
            patVal <- forAll genIntegerPattern
            let patMap = elementMap patKey patVal
                patInKeys = inKeysMap patKey patMap
                predicate = mkEquals_ (Test.Bool.asInternal True) patInKeys
            (===) (Test.Bool.asPattern True) =<< evaluateT patInKeys
            (===) Pattern.top                =<< evaluateT predicate
        )

-- | Check that simplification is carried out on map elements.
test_simplify :: TestTree
test_simplify =
    testCaseWithSMT
        "simplify builtin Map elements"
        $ do
            let
                x =
                    mkElemVar $ ElementVariable Variable
                        { variableName = testId "x"
                        , variableCounter = mempty
                        , variableSort = intSort
                        }
                key = Test.Int.asInternal 1
                original = asTermLike $ Map.fromList [(key, mkAnd x mkTop_)]
                expected = asPattern $ Map.fromList [(key, x)]
            actual <- evaluate original
            assertEqual "expected simplified Map" expected actual

-- | Maps with symbolic keys are not simplified.
test_symbolic :: TestTree
test_symbolic =
    testPropertyWithSolver
        "builtin functions are evaluated on symbolic keys"
        (do
            elements <- forAll $ genMapSortedVariable intSort genIntegerPattern
            let varMap = Map.mapKeys mkElemVar elements
                patMap = asSymbolicPattern varMap
                expect = asVariablePattern varMap
            if Map.null elements
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

mockHookTools :: SmtMetadataTools Hook
mockHookTools = StepperAttributes.hook <$> Mock.metadataTools

-- | Construct a pattern for a map which may have symbolic keys.
asSymbolicPattern
    :: Map (TermLike Variable) (TermLike Variable)
    -> TermLike Variable
asSymbolicPattern result
    | Map.null result =
        applyUnit
    | otherwise =
        foldr1 applyConcat (applyElement <$> Map.toAscList result)
  where
    applyUnit = mkApplySymbol unitMapSymbol []
    applyElement (key, value) = elementMap key value
    applyConcat map1 map2 = concatMap map1 map2

{- | Unify two maps with concrete keys and variable values.
 -}
test_unifyConcrete :: TestTree
test_unifyConcrete =
    testPropertyWithSolver
        "unify maps with concrete keys and symbolic values"
        (do
            let genVariablePair =
                    (,) <$> genIntVariable <*> genIntVariable
                  where
                    genIntVariable =
                        standaloneGen $ mkElemVar <$> elementVariableGen intSort
            map12 <- forAll (genConcreteMap genVariablePair)
            let map1 = fst <$> map12
                map2 = snd <$> map12
                patExpect = asTermLike $ uncurry mkAnd <$> map12
                patActual = mkAnd (asTermLike map1) (asTermLike map2)
                predicate = mkEquals_ patExpect patActual
            expect <- evaluateT patExpect
            actual <- evaluateT patActual
            (===) expect actual
            (===) Pattern.top =<< evaluateT predicate
        )


-- Given a function to scramble the arguments to concat, i.e.,
-- @id@ or @reverse@, produces a pattern of the form
-- `MapItem(absInt(K:Int), absInt(V:Int)) Rest:Map`, or
-- `Rest:Map MapItem(absInt(K:Int), absInt(V:Int))`, respectively.
selectFunctionPattern
    :: ElementVariable Variable           -- ^key variable
    -> ElementVariable Variable           -- ^value variable
    -> ElementVariable Variable           -- ^map variable
    -> (forall a . [a] -> [a])            -- ^scrambling function
    -> TermLike Variable
selectFunctionPattern keyVar valueVar mapVar permutation  =
    mkApplySymbol concatMapSymbol $ permutation [singleton, mkElemVar mapVar]
  where
    key = mkApplySymbol absIntSymbol  [mkElemVar keyVar]
    value = mkApplySymbol absIntSymbol  [mkElemVar valueVar]
    singleton = mkApplySymbol elementMapSymbol [ key, value ]

makeElementSelect
    :: ElementVariable Variable -> ElementVariable Variable -> TermLike Variable
makeElementSelect keyVar valueVar =
    mkApplySymbol elementMapSymbol [mkElemVar keyVar, mkElemVar valueVar]

makeElementLookup
    :: TermLike Concrete -> ElementVariable Variable -> TermLike Variable
makeElementLookup key valueVar =
    mkApplySymbol
        elementMapSymbol
        [TermLike.fromConcrete key, mkElemVar valueVar]

-- Given a function to scramble the arguments to concat, i.e.,
-- @id@ or @reverse@, produces a pattern of the form
-- `MapItem(K:Int, V:Int) Rest:Map`, or `Rest:Map MapItem(K:Int, V:Int)`,
-- respectively.
selectPattern
    :: ElementVariable Variable           -- ^key variable
    -> ElementVariable Variable           -- ^value variable
    -> ElementVariable Variable           -- ^map variable
    -> (forall a . [a] -> [a])            -- ^scrambling function
    -> TermLike Variable
selectPattern keyVar valueVar mapVar permutation  =
    mkApplySymbol concatMapSymbol $ permutation [element, mkElemVar mapVar]
  where
    element = makeElementSelect keyVar valueVar

addSelectElement
    :: ElementVariable Variable          -- ^key variable
    -> ElementVariable Variable          -- ^value variable
    -> TermLike Variable
    -> TermLike Variable
addSelectElement keyVar valueVar mapPattern  =
    mkApplySymbol concatMapSymbol [element, mapPattern]
  where
    element = makeElementSelect keyVar valueVar

addLookupElement
    :: TermLike Concrete                 -- ^key
    -> ElementVariable Variable          -- ^value variable
    -> TermLike Variable
    -> TermLike Variable
addLookupElement key valueVar mapPattern  =
    mkApplySymbol concatMapSymbol [element, mapPattern]
  where
    element = makeElementLookup key valueVar

test_unifyEmptyWithEmpty :: TestTree
test_unifyEmptyWithEmpty =
    testPropertyWithSolver "Unify empty map pattern with empty map DV" $ do
        -- Map.empty /\ mapUnit
        (emptyMapDV `unifiesWithMulti` emptyMapPattern) [expect]
        -- mapUnit /\ Map.empty
        (emptyMapPattern `unifiesWithMulti` emptyMapDV) [expect]
  where
    emptyMapDV = asInternal []
    emptyMapPattern = asTermLike Map.empty
    expect =
        Conditional
            { term = emptyMapDV
            , predicate = makeTruePredicate
            , substitution = Substitution.unsafeWrap []
            }

test_unifySelectFromEmpty :: TestTree
test_unifySelectFromEmpty =
    testPropertyWithSolver "unify an empty map with a selection pattern" $ do
        keyVar <- forAll (standaloneGen $ elementVariableGen intSort)
        valueVar <- forAll (standaloneGen $ elementVariableGen intSort)
        mapVar <- forAll (standaloneGen $ elementVariableGen mapSort)
        let variables = [ keyVar, valueVar, mapVar ]
        Monad.unless (distinctVariables variables) discard
        let selectPat       = selectPattern keyVar valueVar mapVar id
            selectPatRev    = selectPattern keyVar valueVar mapVar reverse
            fnSelectPat     = selectFunctionPattern keyVar valueVar mapVar id
            fnSelectPatRev  =
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
    emptyMap = asTermLike Map.empty
    doesNotUnifyWith pat1 pat2 =
        (===) Pattern.bottom =<< evaluateT (mkAnd pat1 pat2)

test_unifySelectFromSingleton :: TestTree
test_unifySelectFromSingleton =
    testPropertyWithSolver
        "unify a singleton map with a variable selection pattern"
        (do
            key      <- forAll genIntegerPattern
            value    <- forAll genIntegerPattern
            keyVar   <- forAll (standaloneGen $ elementVariableGen intSort)
            valueVar <- forAll (standaloneGen $ elementVariableGen intSort)
            mapVar   <- forAll (standaloneGen $ elementVariableGen mapSort)
            let variables = [keyVar, valueVar, mapVar]
            Monad.unless (distinctVariables variables) discard
            let selectPat      = selectPattern keyVar valueVar mapVar id
                selectPatRev   = selectPattern keyVar valueVar mapVar reverse
                singleton      = asInternal [(key, value)]
                expect =
                    Conditional
                        { term = singleton
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (ElemVar mapVar, asInternal [])
                                , (ElemVar keyVar, key)
                                , (ElemVar valueVar, value)
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
    testPropertyWithSolver
        "unify a singleton map with a singleton variable selection pattern"
        (do
            key <- forAll genIntegerPattern
            value <- forAll genIntegerPattern
            keyVar <- forAll (standaloneGen $ elementVariableGen intSort)
            valueVar <- forAll (standaloneGen $ elementVariableGen intSort)
            let variables = [keyVar, valueVar]
            Monad.unless (distinctVariables variables) discard
            let
                emptyMapPat    = asTermLike Map.empty
                selectPat      = addSelectElement keyVar valueVar emptyMapPat
                singleton      = asInternal [(key, value)]
                expect =
                    Conditional
                        { term = singleton
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (ElemVar keyVar, key)
                                , (ElemVar valueVar, value)
                                ]
                        }
            -- { 5 -> 7 } /\ Item(K:Int, V:Int) Map.unit
            (singleton `unifiesWith` selectPat) expect
            (selectPat `unifiesWith` singleton) expect
        )

test_unifySelectFromSingletonWithoutLeftovers :: TestTree
test_unifySelectFromSingletonWithoutLeftovers =
    testPropertyWithSolver
        "unify a singleton map with an element selection pattern"
        (do
            key <- forAll genIntegerPattern
            value <- forAll genIntegerPattern
            keyVar <- forAll (standaloneGen $ elementVariableGen intSort)
            valueVar <- forAll (standaloneGen $ elementVariableGen intSort)
            let variables = [keyVar, valueVar]
            Monad.unless (distinctVariables variables) discard
            let selectPat = makeElementSelect keyVar valueVar
                singleton = asInternal [(key, value)]
                expect =
                    Conditional
                        { term = singleton
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (ElemVar keyVar, key)
                                , (ElemVar valueVar, value)
                                ]
                        }
            -- { 5 -> 7 } /\ Item(K:Int, V:Int)
            (singleton `unifiesWith` selectPat) expect
            (selectPat `unifiesWith` singleton) expect
        )

test_unifySelectFromTwoElementMap :: TestTree
test_unifySelectFromTwoElementMap =
    testPropertyWithSolver
        "unify a two element map with a variable selection pattern"
        (do
            key1 <- forAll genIntegerPattern
            value1 <- forAll genIntegerPattern
            key2 <- forAll genIntegerPattern
            value2 <- forAll genIntegerPattern
            Monad.when (key1 == key2) discard

            keyVar <- forAll (standaloneGen $ elementVariableGen intSort)
            valueVar <- forAll (standaloneGen $ elementVariableGen intSort)
            mapVar <- forAll (standaloneGen $ elementVariableGen mapSort)
            let variables = [keyVar, valueVar, mapVar]
            Monad.unless (distinctVariables variables) discard

            let selectPat       = selectPattern keyVar valueVar mapVar id
                selectPatRev    = selectPattern keyVar valueVar mapVar reverse
                mapDV = asInternal [(key1, value1), (key2, value2)]
                expect1 =
                    Conditional
                        { term = mapDV
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (ElemVar mapVar, asInternal [(key2, value2)])
                                , (ElemVar keyVar, key1)
                                , (ElemVar valueVar, value1)
                                ]
                        }
                expect2 =
                    Conditional
                        { term = mapDV
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (ElemVar mapVar, asInternal [(key1, value1)])
                                , (ElemVar keyVar, key2)
                                , (ElemVar valueVar, value2)
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
    testPropertyWithSolver
        "unify a two element map with a binary variable selection pattern"
        (do
            key1 <- forAll genIntegerPattern
            value1 <- forAll genIntegerPattern
            key2 <- forAll genIntegerPattern
            value2 <- forAll genIntegerPattern
            Monad.when (key1 == key2) discard

            keyVar1 <- forAll (standaloneGen $ elementVariableGen intSort)
            valueVar1 <- forAll (standaloneGen $ elementVariableGen intSort)
            keyVar2 <- forAll (standaloneGen $ elementVariableGen intSort)
            valueVar2 <- forAll (standaloneGen $ elementVariableGen intSort)
            mapVar <- forAll (standaloneGen $ elementVariableGen mapSort)
            let variables = [keyVar1, keyVar2, valueVar1, valueVar2, mapVar]
            Monad.unless (distinctVariables variables) discard

            let selectPat =
                    addSelectElement keyVar1 valueVar1
                    $ addSelectElement keyVar2 valueVar2
                    $ mkElemVar mapVar
                mapDV = asInternal [(key1, value1), (key2, value2)]
                expect1 =
                    Conditional
                        { term = mapDV
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (ElemVar mapVar, asInternal [])
                                , (ElemVar keyVar1, key1)
                                , (ElemVar keyVar2, key2)
                                , (ElemVar valueVar1, value1)
                                , (ElemVar valueVar2, value2)
                                ]
                        }
                expect2 =
                    Conditional
                        { term = mapDV
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (ElemVar mapVar, asInternal [])
                                , (ElemVar keyVar1, key2)
                                , (ElemVar keyVar2, key1)
                                , (ElemVar valueVar1, value2)
                                , (ElemVar valueVar2, value1)
                                ]
                        }

            -- { 5 } /\ MapItem(X:Int) Rest:Map
            (mapDV `unifiesWithMulti` selectPat) [expect1, expect2]
            (selectPat `unifiesWithMulti` mapDV) [expect1, expect2]
        )

test_unifySameSymbolicKey :: TestTree
test_unifySameSymbolicKey =
    testPropertyWithSolver
        "unify a single element symbolic map with a symbolic selection pattern"
        (do

            value1 <- forAll genIntegerPattern
            keyVar1 <- forAll (standaloneGen $ elementVariableGen intSort)
            valueVar1 <- forAll (standaloneGen $ elementVariableGen intSort)
            mapVar <- forAll (standaloneGen $ elementVariableGen mapSort)
            let variables = [keyVar1, valueVar1, mapVar]
            Monad.unless (distinctVariables variables) discard

            let selectPat =
                    addSelectElement keyVar1 valueVar1
                    $ mkElemVar mapVar
                mapValue =
                    asVariableInternal
                        (Map.singleton (mkElemVar keyVar1) value1)
                expect1 =
                    Conditional
                        { term = mapValue
                        , predicate = makeTruePredicate
                        , substitution =
                            Substitution.unsafeWrap
                                [ (ElemVar mapVar, asInternal [])
                                , (ElemVar valueVar1, value1)
                                ]
                        }

            -- { x -> 5 } /\ MapItem(x:Int, y:Int) Rest:Map
            (mapValue `unifiesWithMulti` selectPat) [expect1]
            (selectPat `unifiesWithMulti` mapValue) [expect1]
        )

test_unifySameSymbolicKeySymbolicOpaque :: TestTree
test_unifySameSymbolicKeySymbolicOpaque =
    testPropertyWithSolver
        "unify two symbolic maps with identical keys and one variable opaque"
        (do
            key1 <- forAll genIntegerPattern
            value1 <- forAll genIntegerPattern
            value2 <- forAll genIntegerPattern

            keyVar2 <- forAll (standaloneGen $ elementVariableGen intSort)
            valueVar1 <- forAll (standaloneGen $ elementVariableGen intSort)
            valueVar2 <- forAll (standaloneGen $ elementVariableGen intSort)
            mapVar1 <- forAll (standaloneGen $ elementVariableGen mapSort)
            mapVar2 <- forAll (standaloneGen $ elementVariableGen mapSort)
            let variables = [keyVar2, valueVar1, valueVar2, mapVar1, mapVar2]
            Monad.unless (distinctVariables variables) discard

            let (minMapVar, maxMapVar) =
                    if mapVar1 < mapVar2
                    then (mapVar1, mapVar2)
                    else (mapVar2, mapVar1)
                selectPat =
                    addLookupElement (unsafeAsConcrete key1) valueVar1
                    $ addSelectElement keyVar2 valueVar2
                    $ mkElemVar mapVar2
                mapValueFromVar mapVar =
                    Ac.asInternal testMetadataTools mapSort
                    $ Domain.wrapAc Domain.NormalizedAc
                        { elementsWithVariables =
                            [Domain.MapElement (mkElemVar keyVar2, value2)]
                        , concreteElements =
                            Map.singleton
                                (unsafeAsConcrete key1)
                                (Domain.MapValue value1)
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
                                [ (ElemVar minMapVar, mkElemVar maxMapVar)
                                , (ElemVar valueVar1, value1)
                                , (ElemVar valueVar2, value2)
                                ]
                        }

            -- { x -> 5 } /\ MapItem(x:Int, y:Int) Rest:Map
            (mapValue `unifiesWithMulti` selectPat) [expect1]
            (selectPat `unifiesWithMulti` mapValue) [expect1]
        )

-- use as (pat1 `unifiesWith` pat2) expect
unifiesWith
    :: HasCallStack
    => TermLike Variable
    -> TermLike Variable
    -> Pattern Variable
    -> PropertyT SMT ()
unifiesWith pat1 pat2 expected =
    unifiesWithMulti pat1 pat2 [expected]

-- use as (pat1 `unifiesWithMulti` pat2) expect
unifiesWithMulti
    :: HasCallStack
    => TermLike Variable
    -> TermLike Variable
    -> [Pattern Variable]
    -> PropertyT SMT ()
unifiesWithMulti pat1 pat2 expectedResults = do
    actualResults <- Trans.lift $ evaluateToList (mkAnd pat1 pat2)
    compareElements (List.sort expectedResults) actualResults
  where
    compareElements [] actuals = [] === actuals
    compareElements expecteds [] =  expecteds === []
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
            }
      = do
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
    testCaseWithSMT
        "unify a concrete Map with a symbolic Map"
        $ do
            actual <- evaluate original
            assertEqual "expected simplified Map" expected actual
  where
    x =
        ElementVariable Variable
            { variableName = testId "x"
            , variableCounter = mempty
            , variableSort = intSort
            }
    v =
        ElementVariable Variable
            { variableName = testId "v"
            , variableCounter = mempty
            , variableSort = intSort
            }
    key :: TermLike Variable
    key = fromConcrete $ Test.Int.asInternal 1
    val = Test.Int.asInternal 2
    concreteMap = asInternal [(key, val)]
    symbolic = asSymbolicPattern $ Map.fromList [(mkElemVar x, mkElemVar v)]
    original =
        mkAnd
            (mkPair intSort mapSort (Test.Int.asInternal 1) concreteMap)
            (mkPair intSort mapSort (mkElemVar x) symbolic)
    expected =
        Conditional
            { term = mkPair intSort mapSort key (asInternal [(key, val)])
            , predicate = Predicate.makeTruePredicate
            , substitution =
                Substitution.unsafeWrap [(ElemVar v, val), (ElemVar x, key)]
            }

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
    testCaseWithSMT
        "unify a concrete Map with a symbolic Map in an axiom"
        $ do
            let concreteMap = asTermLike $ Map.fromList [(key, val)]
            config <- evaluate $ pair symbolicKey concreteMap
            actual <- runStep config axiom
            assertEqual "expected MAP.lookup" expected actual
  where
    x = mkIntVar (testId "x")
    v = mkIntVar (testId "v")
    key = Test.Int.asInternal 1
    symbolicKey = fromConcrete key
    val = Test.Int.asInternal 2
    symbolicMap = asSymbolicPattern $ Map.fromList [(x, v)]
    axiom =
        RewriteRule RulePattern
            { left = mkPair intSort mapSort x symbolicMap
            , antiLeft = Nothing
            , right = v
            , requires = Predicate.makeTruePredicate
            , ensures = Predicate.makeTruePredicate
            , attributes = Default.def
            }
    expected = Right (MultiOr [ pure val ])

test_renormalize :: [TestTree]
test_renormalize =
    [ unchanged "abstract key is unchanged" (mkMap [(x, v)] [] [])
    , becomes "concrete key is normalized"
        (mkMap [(k1, v)] [] [])
        (mkMap [] [(k1, v)] [])
    , becomes "opaque child is flattened"
        (mkMap [] [(k1, v)] [mkMap [] [(k2, v)] []])
        (mkMap [] [(k1, v), (k2, v)] [])
    , becomes "child is flattened and normalized"
        (mkMap [] [(k1, v)] [mkMap [(k2, v)] [] []])
        (mkMap [] [(k1, v), (k2, v)] [])
    , becomes "grandchild is flattened and normalized"
        (mkMap [] [(k1, v)] [mkMap [(x, v)] [] [mkMap [(k2, v)] [] []]])
        (mkMap [(x, v)] [(k1, v), (k2, v)] [])
    , denorm "duplicate key in map"
        (mkMap [(k1, v), (k1, v)] [] [])
    , denorm "duplicate key in child"
        (mkMap [(k1, v)] [] [mkMap [(k1, v)] [] []])
    ]
  where
    x = mkIntVar (testId "x")
    v = mkIntVar (testId "v")
    k1, k2 :: Ord variable => TermLike variable
    k1 = Test.Int.asInternal 1
    k2 = Test.Int.asInternal 2

    becomes
        :: GHC.HasCallStack
        => TestName
        -> NormalizedMap (TermLike Concrete) (TermLike Variable)
        -- ^ original, (possibly) de-normalized map
        -> NormalizedMap (TermLike Concrete) (TermLike Variable)
        -- ^ expected normalized map
        -> TestTree
    becomes name origin expect =
        testCase name $ assertEqual "" (Just expect) (Ac.renormalize origin)

    unchanged
        :: GHC.HasCallStack
        => TestName
        -> NormalizedMap (TermLike Concrete) (TermLike Variable)
        -> TestTree
    unchanged name origin = becomes name origin origin

    denorm
        :: GHC.HasCallStack
        => TestName
        -> NormalizedMap (TermLike Concrete) (TermLike Variable)
        -> TestTree
    denorm name origin =
        testCase name $ assertEqual "" Nothing (Ac.renormalize origin)

    mkMap
        :: [(TermLike Variable, TermLike Variable)]
        -- ^ abstract elements
        -> [(TermLike Concrete, TermLike Variable)]
        -- ^ concrete elements
        -> [NormalizedMap (TermLike Concrete) (TermLike Variable)]
        -- ^ opaque terms
        -> NormalizedMap (TermLike Concrete) (TermLike Variable)
    mkMap abstract concrete opaque =
        Domain.wrapAc $ Domain.NormalizedAc
            { elementsWithVariables = Domain.MapElement <$> abstract
            , concreteElements =
                Map.fromList (Bifunctor.second Domain.MapValue <$> concrete)
            , opaque =
                Ac.asInternal testMetadataTools mapSort <$> opaque
            }

hprop_unparse :: Property
hprop_unparse =
    hpropUnparse
        ( asInternal
        . Map.toList
        . Map.mapKeys fromConcrete
        <$> genConcreteMap genValue
        )
  where
    genValue = Test.Int.asInternal <$> genInteger

-- | Specialize 'Map.asTermLike' to the builtin sort 'mapSort'.
asTermLike :: Map (TermLike Concrete) (TermLike Variable) -> TermLike Variable
asTermLike =
    Reflection.give testMetadataTools Map.asTermLike
    . builtinMap
    . Map.toAscList

-- | Specialize 'Map.asPattern' to the builtin sort 'mapSort'.
asPattern :: Map (TermLike Concrete) (TermLike Variable) -> Pattern Variable
asPattern concreteMap =
    Reflection.give testMetadataTools
    $ Ac.asPattern mapSort
    $ Domain.wrapAc Domain.NormalizedAc
        { elementsWithVariables = []
        , concreteElements = Domain.MapValue <$> concreteMap
        , opaque = []
        }

asVariablePattern
    :: Map (TermLike Variable) (TermLike Variable) -> Pattern Variable
asVariablePattern variableMap =
    Reflection.give testMetadataTools
    $ Ac.asPattern mapSort
    $ Domain.wrapAc Domain.NormalizedAc
        { elementsWithVariables = Domain.MapElement <$> Map.toList variableMap
        , concreteElements = Map.empty
        , opaque = []
        }

asVariableInternal
    :: Map (TermLike Variable) (TermLike Variable) -> TermLike Variable
asVariableInternal variableMap =
    Ac.asInternal testMetadataTools mapSort
    $ Domain.wrapAc Domain.NormalizedAc
        { elementsWithVariables = Domain.MapElement <$> Map.toList variableMap
        , concreteElements = Map.empty
        , opaque = []
        }

-- | Specialize 'Ac.asInternal' to the builtin sort 'mapSort'.
asInternal
    :: [(TermLike Variable, TermLike Variable)]
    -> TermLike Variable
asInternal elements =
    Ac.asInternal testMetadataTools mapSort
    $ Domain.wrapAc Domain.NormalizedAc
        { elementsWithVariables = Domain.wrapElement <$> abstractElements
        , concreteElements
        , opaque = []
        }
  where
    asConcrete element@(key, value) =
        (,) <$> TermLike.asConcrete key <*> pure value
        & maybe (Left element) Right
    (abstractElements, Map.fromList -> concreteElements) =
        asConcrete . Bifunctor.second Domain.MapValue <$> elements
        & Either.partitionEithers

unsafeAsConcrete :: TermLike Variable -> TermLike Concrete
unsafeAsConcrete term =
    case TermLike.asConcrete term of
        Just result -> result
        Nothing -> error "Expected concrete term."

{- | Construct a 'NormalizedMap' from a list of elements and opaque terms.

It is an error if the collection cannot be normalized.

 -}
normalizedMap
    :: GHC.HasCallStack
    => [(TermLike Variable, TermLike Variable)]
    -- ^ (abstract or concrete) elements
    -> [TermLike Variable]
    -- ^ opaque terms
    -> NormalizedMap (TermLike Concrete) (TermLike Variable)
normalizedMap elements opaque =
    Maybe.fromJust . Ac.renormalize . Domain.wrapAc $ Domain.NormalizedAc
        { elementsWithVariables = Domain.MapElement <$> elements
        , concreteElements = Map.empty
        , opaque
        }

-- * Constructors

mkIntVar :: Id -> TermLike Variable
mkIntVar variableName =
    mkElemVar $ ElementVariable
        Variable
            { variableName, variableCounter = mempty, variableSort = intSort }

mockSubstitutionSimplifier
    :: MonadSimplify simplifier => PredicateSimplifier simplifier
mockSubstitutionSimplifier = PredicateSimplifier return

asVariableName :: ElementVariable Variable -> Id
asVariableName = variableName . getElementVariable

distinctVariables :: [ElementVariable Variable] -> Bool
distinctVariables variables =
    length variableNames == length (List.nub variableNames)
  where
    variableNames = map asVariableName variables
