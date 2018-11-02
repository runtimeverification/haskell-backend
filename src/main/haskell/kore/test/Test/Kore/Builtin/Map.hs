module Test.Kore.Builtin.Map where

import Test.QuickCheck
       ( Gen, Property, property, (.&&.), (===), (==>) )
import Test.Tasty.HUnit

import           Control.Error
                 ( runExceptT )
import qualified Data.Bifunctor as Bifunctor
import qualified Data.Default as Default
import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Reflection
                 ( give )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( asPurePattern, fromConcretePurePattern )
import           Kore.AST.Sentence
import qualified Kore.ASTUtils.SmartConstructors as Kore
import           Kore.ASTUtils.SmartPatterns
import           Kore.ASTVerifier.DefinitionVerifier
import           Kore.Attribute.Parser
                 ( ParseAttributes (..) )
import qualified Kore.Builtin as Builtin
import           Kore.Builtin.Hook
                 ( hookAttribute )
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

import           Test.Kore
                 ( idGen, testId )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import qualified Test.Kore.Builtin.Int as Test.Int
import qualified Test.Kore.Builtin.Set as Test.Set
import qualified Test.Kore.Step.MockSimplifiers as Mock

{- |
    @
        lookup{}(unit{}(), _) === \bottom{}()
    @
 -}
prop_lookupUnit :: Integer -> Property
prop_lookupUnit k =
    let patLookup = App_ symbolLookup [App_ symbolUnit [], Test.Int.asPattern k]
        predicate = mkEquals mkBottom patLookup
    in
        allProperties
            [ ExpandedPattern.bottom === evaluate patLookup
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        lookup{}(update{}(m : Map{}, k : Key{}, v : Value{}), k) === v
    @
 -}
prop_lookupUpdate :: (Integer, Integer) -> Map Integer Integer -> Property
prop_lookupUpdate (key, value) map' =
    let patLookup =
            App_ symbolLookup
                [ App_ symbolUpdate [ patMap, patKey , patValue ]
                , patKey
                ]
        patMap =
            asPattern
            $ Map.mapKeys Test.Int.asConcretePattern
            $ Map.map Test.Int.asPattern map'
        patKey = Test.Int.asPattern key
        patValue = Test.Int.asPattern value
        predicate = mkEquals patLookup patValue
    in
        allProperties
            [ Test.Int.asExpandedPattern value === evaluate patLookup
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        concat{}(unit{}(), map : Map{}) === map
    @
 -}
prop_concatUnit :: Map Integer Integer -> Property
prop_concatUnit map' =
    let patConcat2 = App_ symbolConcat [ patUnit, patMap ]
        patConcat1 = App_ symbolConcat [ patMap, patUnit ]
        patUnit = App_ symbolUnit []
        patMap =
            asPattern
            $ Map.mapKeys Test.Int.asConcretePattern
            $ Map.map Test.Int.asPattern map'
        predicate1 = mkEquals patMap patConcat1
        predicate2 = mkEquals patMap patConcat2
    in
        allProperties
            [ evaluate patMap === evaluate patConcat1
            , evaluate patMap === evaluate patConcat2
            , ExpandedPattern.top === evaluate predicate1
            , ExpandedPattern.top === evaluate predicate2
            ]

{- |
    If @key1@ and @key2@ are distinct keys, then
    @
        lookup{}(
            concat{}(
                element{}(key1, value1),
                element{}(key2, value2)
            ),
            key1
        )
        ===
        value1
    @
    and
    @
        lookup{}(
            concat{}(
                element{}(key1, value1),
                element{}(key2, value2)
            ),
            key2
        )
        ===
        value2
    @
 -}
prop_lookupConcatUniqueKeys :: (Integer, Integer) -> (Integer, Integer) -> Property
prop_lookupConcatUniqueKeys (key1, value1) (key2, value2) =
    let patConcat = App_ symbolConcat [ patMap1, patMap2 ]
        patKey1 = Test.Int.asPattern key1
        patKey2 = Test.Int.asPattern key2
        patValue1 = Test.Int.asPattern value1
        patValue2 = Test.Int.asPattern value2
        patMap1 = App_ symbolElement [ patKey1, patValue1 ]
        patMap2 = App_ symbolElement [ patKey2, patValue2 ]
        patLookup1 = App_ symbolLookup [ patConcat, patKey1 ]
        patLookup2 = App_ symbolLookup [ patConcat, patKey2 ]
        predicate =
            mkImplies
                (mkNot (mkEquals patKey1 patKey2))
                (mkAnd
                    (mkEquals patLookup1 patValue1)
                    (mkEquals patLookup2 patValue2)
                )
    in
        allProperties
            [ (key1 /= key2) ==> allProperties
                [ Test.Int.asExpandedPattern value1 === evaluate patLookup1
                , Test.Int.asExpandedPattern value2 === evaluate patLookup2
                ]
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        concat{}(element{}(key, value1), element{}(key, value2)) === \bottom{}()
    @
 -}
prop_concatDuplicateKeys :: Integer -> Integer -> Integer -> Property
prop_concatDuplicateKeys key value1 value2 =
    let patKey = Test.Int.asPattern key
        patValue1 = Test.Int.asPattern value1
        patValue2 = Test.Int.asPattern value2
        patMap1 = App_ symbolElement [ patKey, patValue1 ]
        patMap2 = App_ symbolElement [ patKey, patValue2 ]
        patConcat = App_ symbolConcat [ patMap1, patMap2 ]
        predicate = mkEquals mkBottom patConcat
    in
        allProperties
            [ ExpandedPattern.bottom === evaluate patConcat
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        concat{}(as : Map{}, bs : Map{}) === concat{}(bs, as)
    @
 -}
prop_concatCommutes :: Map Integer Integer -> Map Integer Integer -> Property
prop_concatCommutes map1 map2 =
    let patConcat1 = App_ symbolConcat [ patMap1, patMap2 ]
        patConcat2 = App_ symbolConcat [ patMap2, patMap1 ]
        patMap1 =
            asPattern
            $ Map.mapKeys Test.Int.asConcretePattern
            $ Map.map Test.Int.asPattern map1
        patMap2 =
            asPattern
            $ Map.mapKeys Test.Int.asConcretePattern
            $ Map.map Test.Int.asPattern map2
        predicate = mkEquals patConcat1 patConcat2
    in
        allProperties
            [ evaluate patConcat1 === evaluate patConcat2
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        concat{}(concat{}(as : Map{}, bs : Map{}), cs : Map{})
        ===
        concat{}(as, concat{}(bs, cs))
    @
 -}
prop_concatAssociates
    :: Map Integer Integer
    -> Map Integer Integer
    -> Map Integer Integer
    -> Property
prop_concatAssociates map1 map2 map3 =
    let patMap1 =
            asPattern
            $ Map.mapKeys Test.Int.asConcretePattern
            $ Map.map Test.Int.asPattern map1
        patMap2 =
            asPattern
            $ Map.mapKeys Test.Int.asConcretePattern
            $ Map.map Test.Int.asPattern map2
        patMap3 =
            asPattern
            $ Map.mapKeys Test.Int.asConcretePattern
            $ Map.map Test.Int.asPattern map3
        patConcat12 = App_ symbolConcat [ patMap1, patMap2 ]
        patConcat23 = App_ symbolConcat [ patMap2, patMap3 ]
        patConcat12_3 = App_ symbolConcat [ patConcat12, patMap3 ]
        patConcat1_23 = App_ symbolConcat [ patMap1, patConcat23 ]
        predicate = mkEquals patConcat12_3 patConcat1_23
    in
        allProperties
            [ evaluate patConcat12_3 === evaluate patConcat1_23
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        inKeys{}(unit{}(), key) === \dv{Bool{}}("false")
    @
 -}
prop_inKeysUnit :: Integer -> Property
prop_inKeysUnit key =
    let patKey = Test.Int.asPattern key
        patUnit = App_ symbolUnit []
        patInKeys = App_ symbolInKeys [ patKey, patUnit ]
        predicate = mkEquals (Test.Bool.asPattern False) patInKeys
    in
        allProperties
            [ Test.Bool.asExpandedPattern False === evaluate patInKeys
            , ExpandedPattern.top === evaluate predicate
            ]

prop_keysUnit :: Property
prop_keysUnit =
    let
        patUnit = App_ symbolUnit []
        patKeys = App_ symbolKeys [patUnit]
        predicate = mkEquals (Test.Set.asPattern Set.empty) patKeys
    in
        allProperties
            [ evaluate (Test.Set.asPattern Set.empty) === evaluate patKeys
            , ExpandedPattern.top === evaluate predicate
            ]

prop_keysElement :: (Integer, Integer) -> Property
prop_keysElement (key, value) =
    let
        concrete = Map.singleton key value
        concreteKeys = Map.keysSet concrete
        patConcreteKeys =
            Test.Set.asPattern
            $ Set.map Test.Int.asConcretePattern concreteKeys
        patMap =
            asPattern
            $ Map.mapKeys Test.Int.asConcretePattern
            $ Map.map Test.Int.asPattern concrete
        patSymbolicKeys = App_ symbolKeys [patMap]
        predicate = mkEquals patConcreteKeys patSymbolicKeys
    in
        allProperties
            [ evaluate patConcreteKeys === evaluate patSymbolicKeys
            , ExpandedPattern.top === evaluate predicate
            ]

prop_keys :: Map Integer Integer -> Property
prop_keys map1 =
    let
        keys1 = Map.keysSet map1
        patConcreteKeys =
            Test.Set.asPattern $ Set.map Test.Int.asConcretePattern keys1
        patMap =
            asPattern
            $ Map.mapKeys Test.Int.asConcretePattern
            $ Map.map Test.Int.asPattern map1
        patSymbolicKeys = App_ symbolKeys [patMap]
        predicate = mkEquals patConcreteKeys patSymbolicKeys
    in
        allProperties
            [ evaluate patConcreteKeys === evaluate patSymbolicKeys
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        inKeys{}(element{}(key, value), key) === \dv{Bool{}}("true")
    @
 -}
prop_inKeysElement :: (Integer, Integer) -> Property
prop_inKeysElement (key, value) =
    let patKey = Test.Int.asPattern key
        patValue = Test.Int.asPattern value
        patMap = App_ symbolElement [ patKey, patValue ]
        patInKeys = App_ symbolInKeys [ patKey, patMap ]
        predicate = mkEquals (Test.Bool.asPattern True) patInKeys
    in
        allProperties
            [ Test.Bool.asExpandedPattern True === evaluate patInKeys
            , ExpandedPattern.top === evaluate predicate
            ]

-- | Check that simplification is carried out on map elements.
unit_simplify :: Assertion
unit_simplify =
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
        actual = evaluate original
    in
        assertEqual "Expected simplified Map" expected actual

-- | Maps with symbolic keys are not simplified.
prop_symbolic :: Map Text Integer -> Property
prop_symbolic values =
    let patMap =
            asSymbolicPattern
            $ Map.mapKeys (mkIntVar . testId)
            $ Map.map Test.Int.asPattern values
    in
        not (Map.null values) ==>
        (ExpandedPattern.fromPurePattern patMap === evaluate patMap)

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
prop_unifyConcrete
    :: Set Integer
    -> Gen Property
prop_unifyConcrete keys = do
    map0 <- traverse (const variablesGen) (Map.fromSet (const ()) keys)
    let map12 =
            Map.mapKeys Test.Int.asConcretePattern
            $ Map.map (Bifunctor.bimap asVariablePattern asVariablePattern) map0
        map1 = fst <$> map12
        map2 = snd <$> map12
        patExpect = asPattern $ uncurry mkAnd <$> map12
        patActual = mkAnd (asPattern map1) (asPattern map2)
    (return . allProperties)
        [ evaluate patExpect === evaluate patActual
        , ExpandedPattern.top === evaluate (mkEquals patExpect patActual)
        ]
  where
    asVariablePattern = asPurePattern . VariablePattern
    variablesGen = (,) <$> variableGen <*> variableGen

{- | Unify a concrete map with symbolic-keyed map.

@
(1, 1 |-> 2) ∧ (x, x |-> v)
@

Iterated unification must turn the symbolic key @x@ into a concrete key by
unifying the first element of the pair. This also requires that Map unification
return a partial result for unifying the second element of the pair.

 -}
unit_concretizeKeys :: Assertion
unit_concretizeKeys =
    assertEqual "Expected simplified Map" expected actual
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
    concrete = asPattern $ Map.fromList [(key, val)]
    symbolic = asSymbolicPattern $ Map.fromList [(mkVar x, mkVar v)]
    original =
        mkAnd
            (mkPair Test.Int.intSort mapSort (Test.Int.asPattern 1) concrete)
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
    actual = evaluate original

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
unit_concretizeKeysAxiom :: Assertion
unit_concretizeKeysAxiom =
    assertEqual "Expected MAP.lookup" expected actual
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
    config =
        evaluate
        $ mkPair Test.Int.intSort mapSort
            symbolicKey
            (asPattern $ Map.fromList [(key, val)])
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
    actual = runStep config axiom

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
            , hookedSymbolDecl "MAP.unit" (builtinSymbol "unitMap")
                mapSort []
            , hookedSymbolDecl "MAP.element" (builtinSymbol "elementMap")
                mapSort [Test.Int.intSort, Test.Int.intSort]
            , hookedSymbolDecl "MAP.concat" (builtinSymbol "concatMap")
                mapSort [mapSort, mapSort]
            , hookedSymbolDecl "MAP.lookup" (builtinSymbol "lookupMap")
                Test.Int.intSort [mapSort, Test.Int.intSort]
            , hookedSymbolDecl "MAP.update" (builtinSymbol "updateMap")
                mapSort [mapSort, Test.Int.intSort, Test.Int.intSort]
            , hookedSymbolDecl "MAP.in_keys" (builtinSymbol "inKeysMap")
                Test.Bool.boolSort [Test.Int.intSort, mapSort]
            , hookedSymbolDecl "MAP.keys" (builtinSymbol "keysMap")
                Test.Set.setSort [mapSort]
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

evaluate :: CommonPurePattern Object -> CommonExpandedPattern Object
evaluate pat =
    fst $ evalSimplifier
        $ Pattern.simplify
            tools (Mock.substitutionSimplifier tools) evaluators pat
  where
    tools = extractMetadataTools indexedModule

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

metadataTools :: MetadataTools Object StepperAttributes
testSymbolOrAliasSorts :: SymbolOrAliasSorts Object
metadataTools@MetadataTools { symbolOrAliasSorts = testSymbolOrAliasSorts } =
    extractMetadataTools indexedModule

runStep
    :: CommonExpandedPattern Object
    -- ^ configuration
    -> AxiomPattern Object
    -- ^ axiom
    -> Either
        (StepError Object Variable)
        (CommonExpandedPattern Object, StepProof Object Variable)
runStep configuration axiom =
    (evalSimplifier . runExceptT)
        (stepWithAxiom
            metadataTools
            (substitutionSimplifier metadataTools)
            configuration
            axiom
        )

-- * Generators and properties

allProperties :: [Property] -> Property
allProperties = foldr (.&&.) (property True)

variableGen :: Gen (Variable Object)
variableGen = Variable <$> idGen Object <*> pure Test.Int.intSort

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
