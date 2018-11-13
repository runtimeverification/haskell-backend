module Test.Kore.Builtin.Map where

import           Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import           Test.Tasty
import           Test.Tasty.HUnit

import           Control.Concurrent.MVar
                 ( MVar )
import           Control.Error
                 ( runExceptT )
import qualified Control.Monad as Monad
import           Control.Monad.Reader
                 ( runReaderT )
import qualified Control.Monad.Trans as Trans
import qualified Data.Default as Default
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Reflection
                 ( give )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( fromConcretePurePattern )
import           Kore.AST.Sentence
import qualified Kore.ASTUtils.SmartConstructors as Kore
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.Attribute.Hook
                 ( hookAttribute )
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Builtin as Builtin
import qualified Kore.Builtin.Map as Map
import qualified Kore.Error
import           Kore.IndexedModule.IndexedModule
import           Kore.IndexedModule.MetadataTools
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.AxiomPatterns
import           Kore.Step.BaseStep
import           Kore.Step.Error
import           Kore.Step.ExpandedPattern
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unification.Data
import           SMT
                 ( SMT, Solver )
import qualified SMT

import           Test.Kore
                 ( testId )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import           Test.Kore.Builtin.Int
                 ( genConcreteIntegerPattern, genInteger, genIntegerPattern )
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Builtin.Set as Test.Set
import           Test.Kore.Step.Condition.Evaluator
                 ( genSortedVariable )
import qualified Test.Kore.Step.MockSimplifiers as Mock
import           Test.SMT

genMapInteger :: Gen a -> Gen (Map Integer a)
genMapInteger genElement =
    Gen.map (Range.linear 0 32) ((,) <$> genInteger <*> genElement)

genConcreteMap :: Gen a -> Gen (Map (ConcretePurePattern Object) a)
genConcreteMap genElement =
    Map.mapKeys Test.Int.asConcretePattern <$> genMapInteger genElement

genMapPattern :: Gen (CommonPurePattern Object)
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
            let patLookup = App_ symbolLookup [App_ symbolUnit [], key]
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
                    App_ symbolLookup
                        [ App_ symbolUpdate [ patMap, patKey, patVal ]
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
            let patConcat2 = App_ symbolConcat [ patUnit, patMap ]
                patConcat1 = App_ symbolConcat [ patMap, patUnit ]
                patUnit = App_ symbolUnit []
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
            let patConcat = App_ symbolConcat [ patMap1, patMap2 ]
                patMap1 = App_ symbolElement [ patKey1, patVal1 ]
                patMap2 = App_ symbolElement [ patKey2, patVal2 ]
                patLookup1 = App_ symbolLookup [ patConcat, patKey1 ]
                patLookup2 = App_ symbolLookup [ patConcat, patKey2 ]
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
            let patMap1 = App_ symbolElement [ patKey, patVal1 ]
                patMap2 = App_ symbolElement [ patKey, patVal2 ]
                patConcat = App_ symbolConcat [ patMap1, patMap2 ]
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
            let patConcat1 = App_ symbolConcat [ patMap1, patMap2 ]
                patConcat2 = App_ symbolConcat [ patMap2, patMap1 ]
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
            let patConcat12 = App_ symbolConcat [ patMap1, patMap2 ]
                patConcat23 = App_ symbolConcat [ patMap2, patMap3 ]
                patConcat12_3 = App_ symbolConcat [ patConcat12, patMap3 ]
                patConcat1_23 = App_ symbolConcat [ patMap1, patConcat23 ]
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
            let patUnit = App_ symbolUnit []
                patInKeys = App_ symbolInKeys [ patKey, patUnit ]
                predicate = mkEquals (Test.Bool.asPattern False) patInKeys
            (===) (Test.Bool.asExpandedPattern False) =<< evaluate patInKeys
            (===) ExpandedPattern.top =<< evaluate predicate
        )

newSolver :: IO (MVar Solver)
newSolver = SMT.newSolver SMT.defaultConfig

test_keysUnit :: TestTree
test_keysUnit =
    testCaseWithSolver
        "keys{}(unit{}() : Map{}) === unit{}() : Set{}"
        (\solver -> do
            let
                patUnit = App_ symbolUnit []
                patKeys = App_ symbolKeys [patUnit]
                patExpect = Test.Set.asPattern Set.empty
                predicate = mkEquals patExpect patKeys
            expect <- evaluateWith solver patExpect
            assertEqual "" expect =<< evaluateWith solver patKeys
            assertEqual "" ExpandedPattern.top =<< evaluateWith solver predicate
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
                patSymbolic = App_ symbolKeys [patMap]
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
                patSymbolicKeys = App_ symbolKeys [patMap]
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
            let patMap = App_ symbolElement [ patKey, patVal ]
                patInKeys = App_ symbolInKeys [ patKey, patMap ]
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
                        , variableSort = Test.Int.intSort
                        }
                key = Test.Int.asConcretePattern 1
                original =
                    mkDomainValue mapSort
                    $ BuiltinDomainMap
                    $ Map.fromList [(key, mkAnd x mkTop)]
                expected =
                    ExpandedPattern.fromPurePattern
                    $ mkDomainValue mapSort
                    $ BuiltinDomainMap
                    $ Map.fromList [(key, x)]
            actual <- evaluateWith solver original
            assertEqual "expected simplified Map" expected actual
        )

-- | Maps with symbolic keys are not simplified.
test_symbolic :: TestTree
test_symbolic =
    testPropertyWithSolver
        "builtin functions are not evaluated on symbolic keys"
        (do
            elements <-
                forAll $ genMapSortedVariable
                    Test.Int.intSort
                    genIntegerPattern
            let patMap = asSymbolicPattern (Map.mapKeys Var_ elements)
                expect = ExpandedPattern.fromPurePattern patMap
            if Map.null elements
                then discard
                else (===) expect =<< evaluate patMap
        )

-- | Construct a pattern for a map which may have symbolic keys.
asSymbolicPattern
    :: Map (CommonPurePattern Object) (CommonPurePattern Object)
    -> CommonPurePattern Object
asSymbolicPattern result
    | Map.null result =
        applyUnit
    | otherwise =
        foldr1 applyConcat (applyElement <$> Map.toAscList result)
  where
    applyUnit = mkDomainValue mapSort $ BuiltinDomainMap Map.empty
    applyElement (key, value) = App_ symbolElement [key, value]
    applyConcat map1 map2 = App_ symbolConcat [map1, map2]

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
                    genIntVariable = Var_ <$> genSortedVariable Test.Int.intSort
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
            assertEqual "expected simplified Map" expected actual
        )
  where
    x =
        Variable
            { variableName = testId "x"
            , variableSort = Test.Int.intSort
            }
    v =
        Variable
            { variableName = testId "v"
            , variableSort = Test.Int.intSort
            }
    key = Test.Int.asConcretePattern 1
    symbolicKey = fromConcretePurePattern key
    val = Test.Int.asPattern 2
    concreteMap = asPattern $ Map.fromList [(key, val)]
    symbolic = asSymbolicPattern $ Map.fromList [(mkVar x, mkVar v)]
    original =
        mkAnd
            (mkPair Test.Int.intSort mapSort (Test.Int.asPattern 1) concreteMap)
            (mkPair Test.Int.intSort mapSort (mkVar x) symbolic)
    expected =
        Predicated
            { term =
                mkPair Test.Int.intSort mapSort
                    symbolicKey
                    (asSymbolicPattern $ Map.fromList [(symbolicKey, val)])
            , predicate = Predicate.makeTruePredicate
            , substitution =
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
                    mkPair Test.Int.intSort mapSort
                        symbolicKey
                        (asPattern $ Map.fromList [(key, val)])
            config <- evaluateWith solver pair
            actual <- runStepWith solver config axiom
            assertEqual "expected MAP.lookup" expected actual
        )
  where
    x = mkIntVar (testId "x")
    v = mkIntVar (testId "v")
    key = Test.Int.asConcretePattern 1
    symbolicKey = fromConcretePurePattern key
    val = Test.Int.asPattern 2
    symbolicMap = asSymbolicPattern $ Map.fromList [(x, v)]
    axiom =
        AxiomPattern
            { axiomPatternLeft =
                mkPair Test.Int.intSort mapSort x symbolicMap
            , axiomPatternRight = v
            , axiomPatternRequires = Predicate.makeTruePredicate
            , axiomPatternAttributes = Default.def
            }
    expected =
        Right
            ( Predicated
                { term = val
                , predicate =
                    -- The predicate is not discharged because we do not
                    -- provide functionality axioms for elementMap.
                    give testSymbolOrAliasSorts
                    Predicate.makeCeilPredicate
                    $ asSymbolicPattern
                    $ Map.fromList [(symbolicKey, val)]
                , substitution = []
                }
            , mconcat
                [ stepProof (StepProofVariableRenamings [])
                , stepProof (StepProofUnification EmptyUnificationProof)
                ]
            )

-- | Specialize 'Map.asPattern' to the builtin sort 'mapSort'.
asPattern :: Map.Builtin Variable -> CommonPurePattern Object
Right asPattern = Map.asPattern indexedModule mapSort

-- | Specialize 'Map.asPattern' to the builtin sort 'mapSort'.
asExpandedPattern :: Map.Builtin Variable -> CommonExpandedPattern Object
Right asExpandedPattern = Map.asExpandedPattern indexedModule mapSort

-- | A sort to hook to the builtin @MAP.Map@.
mapSort :: Sort Object
mapSort =
    SortActualSort SortActual
        { sortActualName = testId "Map"
        , sortActualSorts = []
        }

-- | Declare 'mapSort' in a Kore module.
mapSortDecl :: KoreSentence
mapSortDecl =
    (asSentence . SentenceHookedSort) (SentenceSort
        { sentenceSortName =
            let SortActualSort SortActual { sortActualName } = mapSort
            in sortActualName
        , sentenceSortParameters = []
        , sentenceSortAttributes = Attributes [ hookAttribute "MAP.Map" ]
        }
        :: KoreSentenceSort Object)

mapModuleName :: ModuleName
mapModuleName = ModuleName "MAP"

-- | Make an unparameterized builtin symbol with the given name.
builtinSymbol :: Text -> SymbolOrAlias Object
builtinSymbol name =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams = []
        }

symbolUnit :: SymbolOrAlias Object
Right symbolUnit = Map.lookupSymbolUnit mapSort indexedModule

symbolUpdate :: SymbolOrAlias Object
Right symbolUpdate = Map.lookupSymbolUpdate mapSort indexedModule

symbolLookup :: SymbolOrAlias Object
Right symbolLookup = Map.lookupSymbolLookup mapSort indexedModule

symbolElement :: SymbolOrAlias Object
Right symbolElement = Map.lookupSymbolElement mapSort indexedModule

symbolConcat :: SymbolOrAlias Object
Right symbolConcat = Map.lookupSymbolConcat mapSort indexedModule

symbolInKeys :: SymbolOrAlias Object
Right symbolInKeys = Map.lookupSymbolInKeys mapSort indexedModule

symbolKeys :: SymbolOrAlias Object
Right symbolKeys = Map.lookupSymbolKeys mapSort indexedModule

{- | Declare the @MAP@ builtins.
 -}
mapModule :: KoreModule
mapModule =
    Module
        { moduleName = mapModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importKoreModule Test.Bool.boolModuleName
            , importKoreModule Test.Int.intModuleName
            , importKoreModule Test.Set.setModuleName
            , mapSortDecl
            , hookedSymbolDecl
                (builtinSymbol "unitMap")
                mapSort
                []
                [hookAttribute "MAP.unit"]
            , hookedSymbolDecl
                (builtinSymbol "elementMap")
                mapSort
                [Test.Int.intSort, Test.Int.intSort]
                [hookAttribute "MAP.element"]
            , hookedSymbolDecl
                (builtinSymbol "concatMap")
                mapSort
                [mapSort, mapSort]
                [hookAttribute "MAP.concat"]
            , hookedSymbolDecl
                (builtinSymbol "lookupMap")
                Test.Int.intSort
                [mapSort, Test.Int.intSort]
                [hookAttribute "MAP.lookup"]
            , hookedSymbolDecl
                (builtinSymbol "updateMap")
                mapSort
                [mapSort, Test.Int.intSort, Test.Int.intSort]
                [hookAttribute "MAP.update"]
            , hookedSymbolDecl
                (builtinSymbol "inKeysMap")
                Test.Bool.boolSort
                [Test.Int.intSort, mapSort]
                [hookAttribute "MAP.in_keys"]
            , hookedSymbolDecl
                (builtinSymbol "keysMap")
                Test.Set.setSort
                [mapSort]
                [hookAttribute "MAP.keys"]
            ]
        }

testModuleName :: ModuleName
testModuleName = ModuleName "TEST"

testModule :: KoreModule
testModule =
    Module
        { moduleName = testModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importKoreModule Test.Bool.boolModuleName
            , importKoreModule Test.Int.intModuleName
            , importKoreModule Test.Set.setModuleName
            , importKoreModule mapModuleName
            , importKoreModule pairModuleName
            ]
        }

evaluate
    :: CommonPurePattern Object
    -> PropertyT SMT (CommonExpandedPattern Object)
evaluate =
    (<$>) fst
    . Trans.lift
    . evalSimplifier
    . Pattern.simplify testTools testSubstitutionSimplifier evaluators

evaluateWith
    :: MVar Solver
    -> CommonPurePattern Object
    -> IO (CommonExpandedPattern Object)
evaluateWith solver patt = do
    let simplified =
            Pattern.simplify
                testTools
                testSubstitutionSimplifier
                evaluators
                patt
        smt = fst <$> evalSimplifier simplified
    runReaderT (SMT.getSMT smt) solver

testSymbolOrAliasSorts :: SymbolOrAliasSorts Object
testTools :: MetadataTools Object StepperAttributes
testTools@MetadataTools { symbolOrAliasSorts = testSymbolOrAliasSorts } =
    extractMetadataTools indexedModule

testSubstitutionSimplifier :: PredicateSubstitutionSimplifier Object Simplifier
testSubstitutionSimplifier = Mock.substitutionSimplifier testTools

mapDefinition :: KoreDefinition
mapDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules =
            [ Test.Bool.boolModule
            , Test.Int.intModule
            , Test.Set.setModule
            , mapModule
            , pairModule
            , testModule
            ]
        }

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
indexedModules = verify mapDefinition

indexedModule :: KoreIndexedModule StepperAttributes
Just indexedModule = Map.lookup testModuleName indexedModules

evaluators :: Map (Id Object) [Builtin.Function]
evaluators = Builtin.koreEvaluators indexedModule

verify
    :: ParseAttributes a
    => KoreDefinition
    -> Map ModuleName (KoreIndexedModule a)
verify defn =
    either (error . Kore.Error.printError) id
        (verifyAndIndexDefinition attrVerify Builtin.koreVerifiers defn)
  where
    attrVerify = defaultAttributesVerification Proxy

runStepWith
    :: MVar Solver
    -> CommonExpandedPattern Object
    -- ^ configuration
    -> AxiomPattern Object
    -- ^ axiom
    -> IO
        (Either
            (StepError Object Variable)
            (CommonExpandedPattern Object, StepProof Object Variable)
        )
runStepWith solver configuration axiom = do
    let applied =
            runExceptT $ stepWithAxiom
                testTools
                testSubstitutionSimplifier
                configuration
                axiom
        smt = evalSimplifier applied
    runReaderT (SMT.getSMT smt) solver

-- * Generators

-- * Constructors

mkBottom :: CommonPurePattern Object
mkBottom = Kore.mkBottom

mkEquals
    :: CommonPurePattern Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
mkEquals = give testSymbolOrAliasSorts Kore.mkEquals

mkAnd
    :: CommonPurePattern Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
mkAnd = give testSymbolOrAliasSorts Kore.mkAnd

mkTop :: CommonPurePattern Object
mkTop = Kore.mkTop

mkVar :: Variable Object -> CommonPurePattern Object
mkVar = give testSymbolOrAliasSorts Kore.mkVar

mkDomainValue
    :: Sort Object
    -> BuiltinDomain (CommonPurePattern Object)
    -> CommonPurePattern Object
mkDomainValue = give testSymbolOrAliasSorts Kore.mkDomainValue

mkImplies
    :: CommonPurePattern Object
    -> CommonPurePattern Object
    -> CommonPurePattern Object
mkImplies = give testSymbolOrAliasSorts Kore.mkImplies

mkNot :: CommonPurePattern Object -> CommonPurePattern Object
mkNot = give testSymbolOrAliasSorts Kore.mkNot

mkIntVar :: Id Object -> CommonPurePattern Object
mkIntVar variableName =
    mkVar Variable { variableName, variableSort = Test.Int.intSort }

mockSubstitutionSimplifier :: PredicateSubstitutionSimplifier level Simplifier
mockSubstitutionSimplifier =
    PredicateSubstitutionSimplifier
        (\x -> return (x, SimplificationProof))
