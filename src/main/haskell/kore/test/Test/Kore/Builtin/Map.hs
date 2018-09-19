module Test.Kore.Builtin.Map where

import Test.QuickCheck
       ( Property, (.&&.), (===), (==>) )

import           Data.Map
                 ( Map )
import qualified Data.Map as Map
import           Data.Proxy
                 ( Proxy (..) )

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
                 ( Object )
import           Kore.AST.PureML
                 ( CommonPurePattern )
import           Kore.AST.Sentence
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
    let pat = App_ symbolLookup [App_ symbolUnit [], Test.Int.asPattern k]
    in ExpandedPattern.bottom === evaluate pat

{- |
    @
        lookup{}(element{}(k, v), k) === v
    @
 -}
prop_lookupElement :: (Integer, Integer) -> Property
prop_lookupElement (k, v) =
    let pat =
            App_ symbolLookup
                [ App_ symbolElement
                    [ Test.Int.asPattern k
                    , Test.Int.asPattern v
                    ]
                , Test.Int.asPattern k
                ]
    in Test.Int.asExpandedPattern v === evaluate pat

{- |
    If @vs = [v1, v2, ...]@,
    @
        lookup{}(update{}(update{}(..., k, v2), k, v1), k) === v1
    @
    Otherwise, if @vs = []@ then
    @
        lookup{}(unit{}(), k) === \bottom{}()
    @
 -}
prop_lookupUpdates :: (Integer, [Integer]) -> Property
prop_lookupUpdates (k, vs) =
    let applyUpdate _v m =
            App_ symbolUpdate [ m, Test.Int.asPattern k, Test.Int.asPattern _v ]
        patUnit = App_ symbolUnit []
        patUpdates = foldr applyUpdate patUnit vs
        patLookup =
            App_ symbolLookup [ patUpdates, Test.Int.asPattern k ]
        v =
            case vs of
                [] -> Nothing
                (_v : _) -> Just _v
    in
        Test.Int.asPartialExpandedPattern v === evaluate patLookup

prop_concatUnit :: (Integer, Integer) -> Property
prop_concatUnit (k, v) =
    let patConcat =
            App_ symbolConcat [ patUnit, patElement ]
        patUnit = App_ symbolUnit []
        patElement =
            App_ symbolElement [ Test.Int.asPattern k, Test.Int.asPattern v ]
    in
        evaluate patElement === evaluate patConcat

prop_lookupConcatUniqueKeys :: (Integer, Integer) -> (Integer, Integer) -> Property
prop_lookupConcatUniqueKeys (k1, v1) (k2, v2) =
    let patConcat = App_ symbolConcat [ patElement1, patElement2 ]
        patElement1 =
            App_ symbolElement [ Test.Int.asPattern k1, Test.Int.asPattern v1 ]
        patElement2 =
            App_ symbolElement [ Test.Int.asPattern k2, Test.Int.asPattern v2 ]
        patLookup1 =
            App_ symbolLookup [ patConcat, Test.Int.asPattern k1 ]
        patLookup2 =
            App_ symbolLookup [ patConcat, Test.Int.asPattern k2 ]
    in
        (k1 /= k2) ==>
        (.&&.)
            (Test.Int.asExpandedPattern v1 === evaluate patLookup1)
            (Test.Int.asExpandedPattern v2 === evaluate patLookup2)

prop_lookupConcatDuplicateKeys :: Integer -> Integer -> Integer -> Property
prop_lookupConcatDuplicateKeys k v1 v2 =
    let patConcat = App_ symbolConcat [ patElement1, patElement2 ]
        patElement1 =
            App_ symbolElement [ Test.Int.asPattern k, Test.Int.asPattern v1 ]
        patElement2 =
            App_ symbolElement [ Test.Int.asPattern k, Test.Int.asPattern v2 ]
        patLookup =
            App_ symbolLookup [ patConcat, Test.Int.asPattern k ]
    in
        (ExpandedPattern.bottom === evaluate patLookup)

prop_concatCommutes :: (Integer, Integer) -> (Integer, Integer) -> Property
prop_concatCommutes (k1, v1) (k2, v2) =
    let patConcat1 = App_ symbolConcat [ patElement1, patElement2 ]
        patConcat2 = App_ symbolConcat [ patElement2, patElement1 ]
        patElement1 =
            App_ symbolElement [ Test.Int.asPattern k1, Test.Int.asPattern v1 ]
        patElement2 =
            App_ symbolElement [ Test.Int.asPattern k2, Test.Int.asPattern v2 ]
    in
        evaluate patConcat1 === evaluate patConcat2

prop_concatAssociates :: (Integer, Integer) -> (Integer, Integer) -> (Integer, Integer) -> Property
prop_concatAssociates (k1, v1) (k2, v2) (k3, v3) =
    let patConcat12 = App_ symbolConcat [ patElement1, patElement2 ]
        patConcat23 = App_ symbolConcat [ patElement2, patElement3 ]
        patConcat12_3 = App_ symbolConcat [ patConcat12, patElement3 ]
        patConcat1_23 = App_ symbolConcat [ patElement1, patConcat23 ]
        patElement1 =
            App_ symbolElement [ Test.Int.asPattern k1, Test.Int.asPattern v1 ]
        patElement2 =
            App_ symbolElement [ Test.Int.asPattern k2, Test.Int.asPattern v2 ]
        patElement3 =
            App_ symbolElement [ Test.Int.asPattern k3, Test.Int.asPattern v3 ]
    in
        evaluate patConcat12_3 === evaluate patConcat1_23

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
symbols@Map.Symbols
    { symbolUnit
    , symbolElement
    , symbolConcat
    , symbolLookup
    , symbolUpdate
    }
  =
    Map.Symbols
        { symbolUnit = builtinSymbol "unitMap"
        , symbolElement = builtinSymbol "elementMap"
        , symbolConcat = builtinSymbol "concatMap"
        , symbolLookup = builtinSymbol "lookupMap"
        , symbolUpdate = builtinSymbol "updateMap"
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
