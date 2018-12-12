module Test.Kore.Builtin.Map where

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty

import qualified Control.Monad as Monad
import qualified Data.Default as Default
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Reflection
                 ( give )
import qualified Data.Set as Set

import           Kore.AST.Pure
import qualified Kore.ASTUtils.SmartConstructors as Kore
import           Kore.ASTUtils.SmartPatterns
import qualified Kore.Builtin.Map as Map
import qualified Kore.Domain.Builtin as Domain
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.AxiomPatterns
import           Kore.Step.BaseStep
import           Kore.Step.ExpandedPattern
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
import           Kore.Unification.Data
import qualified Kore.Unification.Substitution as Substitution

import           Test.Kore
                 ( testId )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import           Test.Kore.Builtin.Definition
import           Test.Kore.Builtin.Int
                 ( genConcreteIntegerPattern, genInteger, genIntegerPattern )
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Builtin.Set as Test.Set
import           Test.Kore.Step.Condition.Evaluator
                 ( genSortedVariable )
import           Test.SMT
import           Test.Tasty.HUnit.Extensions

genMapInteger :: Gen a -> Gen (Map Integer a)
genMapInteger genElement =
    Gen.map (Range.linear 0 32) ((,) <$> genInteger <*> genElement)

genConcreteMap :: Gen a -> Gen (Map (ConcreteStepPattern Object) a)
genConcreteMap genElement =
    Map.mapKeys Test.Int.asConcretePattern <$> genMapInteger genElement

genMapPattern :: Gen (CommonStepPattern Object)
genMapPattern = asPattern <$> genConcreteMap genIntegerPattern

genMapSortedVariable
    :: MetaOrObject level
    => Sort level
    -> Gen a
    -> Gen (Map (Variable level) a)
genMapSortedVariable sort genElement =
    Gen.map
        (Range.linear 0 32)
        ((,) <$> genSortedVariable sort <*> genElement)

test_lookupUnit :: TestTree
test_lookupUnit =
    testPropertyWithSolver
        "lookup{}(unit{}(), key) === \\bottom{}()"
        (do
            key <- forAll genIntegerPattern
            let patLookup = App_ lookupMapSymbol [App_ unitMapSymbol [], key]
                predicate = mkEquals mkBottom patLookup
            (===) ExpandedPattern.bottom =<< evaluate patLookup
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_lookupUpdate :: TestTree
test_lookupUpdate =
    testPropertyWithSolver
        "lookup{}(update{}(map, key, val), key) === val"
        (do
            patKey <- forAll genIntegerPattern
            patVal <- forAll genIntegerPattern
            patMap <- forAll genMapPattern
            let patLookup =
                    App_ lookupMapSymbol
                        [ App_ updateMapSymbol [ patMap, patKey, patVal ]
                        , patKey
                        ]
                predicate = mkEquals patLookup patVal
                expect = ExpandedPattern.fromPurePattern patVal
            (===) expect =<< evaluate patLookup
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_concatUnit :: TestTree
test_concatUnit =
    testPropertyWithSolver
        "concat{}(unit{}(), map) === concat{}(map, unit{}()) === map"
        (do
            patMap <- forAll genMapPattern
            let patConcat2 = App_ concatMapSymbol [ patUnit, patMap ]
                patConcat1 = App_ concatMapSymbol [ patMap, patUnit ]
                patUnit = App_ unitMapSymbol []
                predicate1 = mkEquals patMap patConcat1
                predicate2 = mkEquals patMap patConcat2
            expect <- evaluate patMap
            (===) expect =<< evaluate patConcat1
            (===) expect =<< evaluate patConcat2
            (===) ExpandedPattern.top =<< evaluate predicate1
            (===) ExpandedPattern.top =<< evaluate predicate2
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
            let patConcat = App_ concatMapSymbol [ patMap1, patMap2 ]
                patMap1 = App_ elementMapSymbol [ patKey1, patVal1 ]
                patMap2 = App_ elementMapSymbol [ patKey2, patVal2 ]
                patLookup1 = App_ lookupMapSymbol [ patConcat, patKey1 ]
                patLookup2 = App_ lookupMapSymbol [ patConcat, patKey2 ]
                predicate =
                    mkImplies
                        (mkNot (mkEquals patKey1 patKey2))
                        (mkAnd
                            (mkEquals patLookup1 patVal1)
                            (mkEquals patLookup2 patVal2)
                        )
                expect1 = ExpandedPattern.fromPurePattern patVal1
                expect2 = ExpandedPattern.fromPurePattern patVal2
            (===) expect1 =<< evaluate patLookup1
            (===) expect2 =<< evaluate patLookup2
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_concatDuplicateKeys :: TestTree
test_concatDuplicateKeys =
    testPropertyWithSolver
        "concat{}(element{}(key, val1), element{}(key, val2)) === \\bottom{}()"
        (do
            patKey <- forAll genIntegerPattern
            patVal1 <- forAll genIntegerPattern
            patVal2 <- forAll genIntegerPattern
            let patMap1 = App_ elementMapSymbol [ patKey, patVal1 ]
                patMap2 = App_ elementMapSymbol [ patKey, patVal2 ]
                patConcat = App_ concatMapSymbol [ patMap1, patMap2 ]
                predicate = mkEquals mkBottom patConcat
            (===) ExpandedPattern.bottom =<< evaluate patConcat
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_concatCommutes :: TestTree
test_concatCommutes =
    testPropertyWithSolver
        "concat{}(as, bs) === concat{}(bs, as)"
        (do
            patMap1 <- forAll genMapPattern
            patMap2 <- forAll genMapPattern
            let patConcat1 = App_ concatMapSymbol [ patMap1, patMap2 ]
                patConcat2 = App_ concatMapSymbol [ patMap2, patMap1 ]
                predicate = mkEquals patConcat1 patConcat2
            actual1 <- evaluate patConcat1
            actual2 <- evaluate patConcat2
            (===) actual1 actual2
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_concatAssociates :: TestTree
test_concatAssociates =
    testPropertyWithSolver
        "concat{}(concat{}(as, bs), cs) === concat{}(as, concat{}(bs, cs))"
        (do
            patMap1 <- forAll genMapPattern
            patMap2 <- forAll genMapPattern
            patMap3 <- forAll genMapPattern
            let patConcat12 = App_ concatMapSymbol [ patMap1, patMap2 ]
                patConcat23 = App_ concatMapSymbol [ patMap2, patMap3 ]
                patConcat12_3 = App_ concatMapSymbol [ patConcat12, patMap3 ]
                patConcat1_23 = App_ concatMapSymbol [ patMap1, patConcat23 ]
                predicate = mkEquals patConcat12_3 patConcat1_23
            actual12_3 <- evaluate patConcat12_3
            actual1_23 <- evaluate patConcat1_23
            (===) actual12_3 actual1_23
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_inKeysUnit :: TestTree
test_inKeysUnit =
    testPropertyWithSolver
        "inKeys{}(unit{}(), key) === \\dv{Bool{}}(\"false\")"
        (do
            patKey <- forAll genIntegerPattern
            let patUnit = App_ unitMapSymbol []
                patInKeys = App_ inKeysMapSymbol [ patKey, patUnit ]
                predicate = mkEquals (Test.Bool.asPattern False) patInKeys
            (===) (Test.Bool.asExpandedPattern False) =<< evaluate patInKeys
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_keysUnit :: TestTree
test_keysUnit =
    testCaseWithSolver
        "keys{}(unit{}() : Map{}) === unit{}() : Set{}"
        (\solver -> do
            let
                patUnit = App_ unitMapSymbol []
                patKeys = App_ keysMapSymbol [patUnit]
                patExpect = Test.Set.asPattern Set.empty
                predicate = mkEquals patExpect patKeys
            expect <- evaluateWith solver patExpect
            assertEqualWithExplanation "" expect =<< evaluateWith solver patKeys
            assertEqualWithExplanation "" ExpandedPattern.top =<< evaluateWith solver predicate
        )

test_keysElement :: TestTree
test_keysElement =
    testPropertyWithSolver
        "keys{}(element{}(key, _) : Map{}) === element{}(key) : Set{}"
        (do
            key <- forAll genConcreteIntegerPattern
            val <- forAll genIntegerPattern
            let patMap = asPattern $ Map.singleton key val
                patKeys = Test.Set.asPattern $ Set.singleton key
                patSymbolic = App_ keysMapSymbol [patMap]
                predicate = mkEquals patKeys patSymbolic
            expect <- evaluate patKeys
            (===) expect =<< evaluate patSymbolic
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_keys :: TestTree
test_keys =
    testPropertyWithSolver
        "MAP.keys"
        (do
            map1 <- forAll (genConcreteMap genIntegerPattern)
            let keys1 = Map.keysSet map1
                patConcreteKeys = Test.Set.asPattern keys1
                patMap = asPattern map1
                patSymbolicKeys = App_ keysMapSymbol [patMap]
                predicate = mkEquals patConcreteKeys patSymbolicKeys
            expect <- evaluate patConcreteKeys
            (===) expect =<< evaluate patSymbolicKeys
            (===) ExpandedPattern.top =<< evaluate predicate
        )

test_inKeysElement :: TestTree
test_inKeysElement =
    testPropertyWithSolver
        "inKeys{}(element{}(key, _), key) === \\dv{Bool{}}(\"true\")"
        (do
            patKey <- forAll genIntegerPattern
            patVal <- forAll genIntegerPattern
            let patMap = App_ elementMapSymbol [ patKey, patVal ]
                patInKeys = App_ inKeysMapSymbol [ patKey, patMap ]
                predicate = mkEquals (Test.Bool.asPattern True) patInKeys
            (===) (Test.Bool.asExpandedPattern True) =<< evaluate patInKeys
            (===) ExpandedPattern.top =<< evaluate predicate
        )

-- | Check that simplification is carried out on map elements.
test_simplify :: TestTree
test_simplify =
    testCaseWithSolver
        "simplify builtin Map elements"
        (\solver -> do
            let
                x =
                    mkVar Variable
                        { variableName = testId "x"
                        , variableSort = intSort
                        }
                key = Test.Int.asConcretePattern 1
                original =
                    mkDomainValue mapSort
                    $ Domain.BuiltinMap
                    $ Map.fromList [(key, mkAnd x mkTop)]
                expected =
                    ExpandedPattern.fromPurePattern
                    $ mkDomainValue mapSort
                    $ Domain.BuiltinMap
                    $ Map.fromList [(key, x)]
            actual <- evaluateWith solver original
            assertEqualWithExplanation "expected simplified Map" expected actual
        )

-- | Maps with symbolic keys are not simplified.
test_symbolic :: TestTree
test_symbolic =
    testPropertyWithSolver
        "builtin functions are not evaluated on symbolic keys"
        (do
            elements <- forAll $ genMapSortedVariable intSort genIntegerPattern
            let patMap = asSymbolicPattern (Map.mapKeys Var_ elements)
                expect = ExpandedPattern.fromPurePattern patMap
            if Map.null elements
                then discard
                else (===) expect =<< evaluate patMap
        )

-- | Construct a pattern for a map which may have symbolic keys.
asSymbolicPattern
    :: Map (CommonStepPattern Object) (CommonStepPattern Object)
    -> CommonStepPattern Object
asSymbolicPattern result
    | Map.null result =
        applyUnit
    | otherwise =
        foldr1 applyConcat (applyElement <$> Map.toAscList result)
  where
    applyUnit = mkDomainValue mapSort $ Domain.BuiltinMap Map.empty
    applyElement (key, value) = App_ elementMapSymbol [key, value]
    applyConcat map1 map2 = App_ concatMapSymbol [map1, map2]

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
                    genIntVariable = Var_ <$> genSortedVariable intSort
            map12 <- forAll (genConcreteMap genVariablePair)
            let map1 = fst <$> map12
                map2 = snd <$> map12
                patExpect = asPattern $ uncurry mkAnd <$> map12
                patActual = mkAnd (asPattern map1) (asPattern map2)
                predicate = mkEquals patExpect patActual
            expect <- evaluate patExpect
            actual <- evaluate patActual
            (===) expect actual
            (===) ExpandedPattern.top =<< evaluate predicate
        )

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
    testCaseWithSolver
        "unify a concrete Map with a symbolic Map"
        (\solver -> do
            actual <- evaluateWith solver original
            assertEqualWithExplanation "expected simplified Map" expected actual
        )
  where
    x =
        Variable
            { variableName = testId "x"
            , variableSort = intSort
            }
    v =
        Variable
            { variableName = testId "v"
            , variableSort = intSort
            }
    key = Test.Int.asConcretePattern 1
    symbolicKey = fromConcretePurePattern key
    val = Test.Int.asPattern 2
    concreteMap = asPattern $ Map.fromList [(key, val)]
    symbolic = asSymbolicPattern $ Map.fromList [(mkVar x, mkVar v)]
    original =
        mkAnd
            (mkPair intSort mapSort (Test.Int.asPattern 1) concreteMap)
            (mkPair intSort mapSort (mkVar x) symbolic)
    expected =
        Predicated
            { term =
                mkPair intSort mapSort
                    symbolicKey
                    (asSymbolicPattern $ Map.fromList [(symbolicKey, val)])
            , predicate = Predicate.makeTruePredicate
            , substitution =
                Substitution.unsafeWrap
                [ (v, val)
                , (x, symbolicKey)
                ]
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
    testCaseWithSolver
        "unify a concrete Map with a symbolic Map in an axiom"
        (\solver -> do
            let pair =
                    mkPair intSort mapSort
                        symbolicKey
                        (asPattern $ Map.fromList [(key, val)])
            config <- evaluateWith solver pair
            actual <- runStepWith solver config axiom
            assertEqualWithExplanation "expected MAP.lookup" expected actual
        )
  where
    x = mkIntVar (testId "x")
    v = mkIntVar (testId "v")
    key = Test.Int.asConcretePattern 1
    symbolicKey = fromConcretePurePattern key
    val = Test.Int.asPattern 2
    symbolicMap = asSymbolicPattern $ Map.fromList [(x, v)]
    axiom =
        RewriteRule RulePattern
            { left = mkPair intSort mapSort x symbolicMap
            , right = v
            , requires = Predicate.makeTruePredicate
            , attributes = Default.def
            }
    expected =
        Right
            ( Predicated
                { term = val
                , predicate = Predicate.makeTruePredicate
                , substitution = mempty
                }
            , mconcat
                [ stepProof (StepProofVariableRenamings [])
                , stepProof (StepProofUnification EmptyUnificationProof)
                ]
            )

-- | Specialize 'Map.asPattern' to the builtin sort 'mapSort'.
asPattern :: Map.Builtin Variable -> CommonStepPattern Object
Right asPattern = Map.asPattern verifiedModule mapSort

-- | Specialize 'Map.asPattern' to the builtin sort 'mapSort'.
asExpandedPattern :: Map.Builtin Variable -> CommonExpandedPattern Object
Right asExpandedPattern = Map.asExpandedPattern verifiedModule mapSort

-- * Constructors

mkBottom :: CommonStepPattern Object
mkBottom = Kore.mkBottom

mkEquals
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> CommonStepPattern Object
mkEquals = give testSymbolOrAliasSorts Kore.mkEquals

mkAnd
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> CommonStepPattern Object
mkAnd = give testSymbolOrAliasSorts Kore.mkAnd

mkTop :: CommonStepPattern Object
mkTop = Kore.mkTop

mkVar :: Variable Object -> CommonStepPattern Object
mkVar = give testSymbolOrAliasSorts Kore.mkVar

mkDomainValue
    :: Sort Object
    -> Domain.Builtin (CommonStepPattern Object)
    -> CommonStepPattern Object
mkDomainValue = give testSymbolOrAliasSorts Kore.mkDomainValue

mkImplies
    :: CommonStepPattern Object
    -> CommonStepPattern Object
    -> CommonStepPattern Object
mkImplies = give testSymbolOrAliasSorts Kore.mkImplies

mkNot :: CommonStepPattern Object -> CommonStepPattern Object
mkNot = give testSymbolOrAliasSorts Kore.mkNot

mkIntVar :: Id Object -> CommonStepPattern Object
mkIntVar variableName =
    mkVar Variable { variableName, variableSort = intSort }

mockSubstitutionSimplifier :: PredicateSubstitutionSimplifier level Simplifier
mockSubstitutionSimplifier =
    PredicateSubstitutionSimplifier
        (\x -> return (x, SimplificationProof))
