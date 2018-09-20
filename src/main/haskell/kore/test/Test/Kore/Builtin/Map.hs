module Test.Kore.Builtin.Map where

import Test.QuickCheck
       ( Property, property, (.&&.), (===), (==>) )

import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )
import           Data.Reflection
                 ( give )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.PureML
                 ( CommonPurePattern )
import           Kore.AST.Sentence
import           Kore.ASTUtils.SmartConstructors
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
import           Kore.Step.ExpandedPattern
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )

import           Test.Kore
                 ( testId )
import qualified Test.Kore.Builtin.Bool as Test.Bool
import           Test.Kore.Builtin.Builtin
import qualified Test.Kore.Builtin.Int as Test.Int

{- |
    @
        lookup{}(unit{}(), _) === \bottom{}()
    @
 -}
prop_lookupUnit :: Integer -> Property
prop_lookupUnit k =
    let patLookup = App_ symbolLookup [App_ symbolUnit [], Test.Int.asPattern k]
        predicate = give testSortTools $ mkEquals mkBottom patLookup
    in
        allProperties
            [ ExpandedPattern.bottom === evaluate patLookup
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        lookup{}(element{}(k, v), k) === v
    @
 -}
prop_lookupElement :: (Integer, Integer) -> Property
prop_lookupElement (key, value) =
    let patLookup =
            App_ symbolLookup
                [ App_ symbolElement [ patKey , patValue ]
                , patKey
                ]
        patKey = Test.Int.asPattern key
        patValue = Test.Int.asPattern value
        predicate = give testSortTools $ mkEquals patLookup patValue
    in
        allProperties
            [ Test.Int.asExpandedPattern value === evaluate patLookup
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    Let @vs = [v1, v2, ...]@ and let @updates@ be the map constructed by
    assigning @k |-> v@ with all the @vs@ from right to left, i.e.
    @
        updates = update{}(update{}(..., k, v2), k, v1)
    @
    Then,
    @
        lookup{}(updates, k) === v1
    @
    Otherwise, if @vs = []@ then
    @
        lookup{}(unit{}(), k) === \bottom{}()
    @
 -}
prop_lookupUpdates :: (Integer, [Integer]) -> Property
prop_lookupUpdates (key, values) =
    let applyUpdate _v _map =
            App_ symbolUpdate [ _map, patKey, Test.Int.asPattern _v ]
        patKey = Test.Int.asPattern key
        patUnit = App_ symbolUnit []
        patUpdates = foldr applyUpdate patUnit values
        patLookup = App_ symbolLookup [ patUpdates, patKey ]
        value =
            case values of
                [] -> Nothing
                (_v : _) -> Just _v
        patValue = maybe mkBottom Test.Int.asPattern value
        predicate = give testSortTools $ mkEquals patValue patLookup
    in
        allProperties
            [ Test.Int.asPartialExpandedPattern value === evaluate patLookup
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    @
        concat{}(unit{}(), element{}(key, value)) === element{}(key, value)
    @
 -}
prop_concatUnit :: (Integer, Integer) -> Property
prop_concatUnit (key, value) =
    let patConcat = App_ symbolConcat [ patUnit, patElement ]
        patUnit = App_ symbolUnit []
        patKey = Test.Int.asPattern key
        patValue = Test.Int.asPattern value
        patElement = App_ symbolElement [ patKey, patValue ]
        predicate = give testSortTools $ mkEquals patElement patConcat
    in
        allProperties
            [ evaluate patElement === evaluate patConcat
            , ExpandedPattern.top === evaluate predicate
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
            give testSortTools
            (mkImplies
                (mkNot (mkEquals patKey1 patKey2))
                (mkAnd
                    (mkEquals patLookup1 patValue1)
                    (mkEquals patLookup2 patValue2)
                )
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
        predicate = give testSortTools (mkEquals mkBottom patConcat)
    in
        allProperties
            [ ExpandedPattern.bottom === evaluate patConcat
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    Let @a = element{}(key1, value1)@ and @b = element{}(key2, value2)@; then
    @
        concat{}(a, b) === concat{}(b, a)
    @
 -}
prop_concatCommutes :: (Integer, Integer) -> (Integer, Integer) -> Property
prop_concatCommutes (key1, value1) (key2, value2) =
    let patConcat1 = App_ symbolConcat [ patMap1, patMap2 ]
        patConcat2 = App_ symbolConcat [ patMap2, patMap1 ]
        patKey1 = Test.Int.asPattern key1
        patValue1 = Test.Int.asPattern value1
        patKey2 = Test.Int.asPattern key2
        patValue2 = Test.Int.asPattern value2
        patMap1 = App_ symbolElement [ patKey1, patValue1 ]
        patMap2 = App_ symbolElement [ patKey2, patValue2 ]
        predicate = give testSortTools (mkEquals patConcat1 patConcat2)
    in
        allProperties
            [ evaluate patConcat1 === evaluate patConcat2
            , ExpandedPattern.top === evaluate predicate
            ]

{- |
    Let @a = element{}(key1, value1)@, @b = element{}(key2, value2)@
    and @c = element{}(key3, value3)@; then
    @
        concat{}(concat{}(a, b), c) === concat{}(a, concat{}(b, c))
    @
 -}
prop_concatAssociates :: (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer) -> Property
prop_concatAssociates (key1, value1) (key2, value2) (key3, value3) =
    let patKey1 = Test.Int.asPattern key1
        patValue1 = Test.Int.asPattern value1
        patKey2 = Test.Int.asPattern key2
        patValue2 = Test.Int.asPattern value2
        patKey3 = Test.Int.asPattern key3
        patValue3 = Test.Int.asPattern value3
        patMap1 = App_ symbolElement [ patKey1, patValue1 ]
        patMap2 = App_ symbolElement [ patKey2, patValue2 ]
        patMap3 = App_ symbolElement [ patKey3, patValue3 ]
        patConcat12 = App_ symbolConcat [ patMap1, patMap2 ]
        patConcat23 = App_ symbolConcat [ patMap2, patMap3 ]
        patConcat12_3 = App_ symbolConcat [ patConcat12, patMap3 ]
        patConcat1_23 = App_ symbolConcat [ patMap1, patConcat23 ]
        predicate = give testSortTools (mkEquals patConcat12_3 patConcat1_23)
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
        predicate =
            give testSortTools (mkEquals (Test.Bool.asPattern False) patInKeys)
    in
        allProperties
            [ Test.Bool.asExpandedPattern False === evaluate patInKeys
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
        predicate =
            give testSortTools
                (mkEquals (Test.Bool.asPattern True) patInKeys)
    in
        allProperties
            [ Test.Bool.asExpandedPattern True === evaluate patInKeys
            , ExpandedPattern.top === evaluate predicate
            ]

-- | Specialize 'Map.asPattern' to the builtin sort 'mapSort'.
asPattern
    :: Map (CommonPurePattern Object) (CommonPurePattern Object)
    -> CommonPurePattern Object
asPattern = Map.asPattern symbols mapSort

-- | Specialize 'Map.asPattern' to the builtin sort 'mapSort'.
asExpandedPattern
    :: Map (CommonPurePattern Object) (CommonPurePattern Object)
    -> CommonExpandedPattern Object
asExpandedPattern = Map.asExpandedPattern symbols mapSort

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

importBool :: KoreSentence
importBool =
    asSentence
        (SentenceImport
            { sentenceImportModuleName = Test.Bool.boolModuleName
            , sentenceImportAttributes = Attributes []
            }
            :: KoreSentenceImport
        )

importInt :: KoreSentence
importInt =
    asSentence
        (SentenceImport
            { sentenceImportModuleName = Test.Int.intModuleName
            , sentenceImportAttributes = Attributes []
            }
            :: KoreSentenceImport
        )

mapModuleName :: ModuleName
mapModuleName = ModuleName "MAP"

-- | Make an unparameterized builtin symbol with the given name.
builtinSymbol :: String -> SymbolOrAlias Object
builtinSymbol name =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams = []
        }

symbols :: Map.Symbols
symbolUnit :: SymbolOrAlias Object
symbolElement :: SymbolOrAlias Object
symbolConcat :: SymbolOrAlias Object
symbolLookup :: SymbolOrAlias Object
symbolUpdate :: SymbolOrAlias Object
symbolInKeys :: SymbolOrAlias Object
symbols@Map.Symbols
    { symbolUnit
    , symbolElement
    , symbolConcat
    , symbolLookup
    , symbolUpdate
    , symbolInKeys
    }
  =
    Map.Symbols
        { symbolUnit = builtinSymbol "unitMap"
        , symbolElement = builtinSymbol "elementMap"
        , symbolConcat = builtinSymbol "concatMap"
        , symbolLookup = builtinSymbol "lookupMap"
        , symbolUpdate = builtinSymbol "updateMap"
        , symbolInKeys = builtinSymbol "inKeysMap"
        }

{- | Declare the @MAP@ builtins.
 -}
mapModule :: KoreModule
mapModule =
    Module
        { moduleName = mapModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importBool
            , importInt
            , mapSortDecl
            , hookedSymbolDecl "MAP.unit" symbolUnit
                mapSort []
            , hookedSymbolDecl "MAP.element" symbolElement
                mapSort [Test.Int.intSort, Test.Int.intSort]
            , hookedSymbolDecl "MAP.concat" symbolConcat
                mapSort [mapSort, mapSort]
            , hookedSymbolDecl "MAP.lookup" symbolLookup
                Test.Int.intSort [mapSort, Test.Int.intSort]
            , hookedSymbolDecl "MAP.update" symbolUpdate
                mapSort [mapSort, Test.Int.intSort, Test.Int.intSort]
            , hookedSymbolDecl "MAP.in_keys" symbolInKeys
                Test.Bool.boolSort [Test.Int.intSort, mapSort]
            ]
        }

evaluate :: CommonPurePattern Object -> CommonExpandedPattern Object
evaluate pat =
    fst $ evalSimplifier $ Pattern.simplify tools evaluators pat
  where
    tools = extractMetadataTools indexedModule

mapDefinition :: KoreDefinition
mapDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules =
            [ Test.Bool.boolModule
            , Test.Int.intModule
            , mapModule
            ]
        }

indexedModules :: Map ModuleName (KoreIndexedModule StepperAttributes)
indexedModules = verify mapDefinition

indexedModule :: KoreIndexedModule StepperAttributes
Just indexedModule = Map.lookup mapModuleName indexedModules

evaluators :: Map (Id Object) [Builtin.Function]
evaluators = Builtin.evaluators Map.builtinFunctions indexedModule

verify
    :: ParseAttributes a
    => KoreDefinition
    -> Map ModuleName (KoreIndexedModule a)
verify defn =
    either (error . Kore.Error.printError) id
        (verifyAndIndexDefinition attrVerify builtinVerifiers defn)
  where
    attrVerify = defaultAttributesVerification Proxy

builtinVerifiers :: Builtin.Verifiers
builtinVerifiers =
    Builtin.Verifiers
        { sortDeclVerifiers = Map.sortDeclVerifiers
        , symbolVerifiers = Map.symbolVerifiers
        , patternVerifier = mempty
        }

testSortTools :: SortTools Object
MetadataTools { sortTools = testSortTools } = extractMetadataTools indexedModule

allProperties :: [Property] -> Property
allProperties = foldr (.&&.) (property True)
