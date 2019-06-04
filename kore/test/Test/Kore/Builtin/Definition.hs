module Test.Kore.Builtin.Definition where

import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.Attribute.Constructor
import           Kore.Attribute.Functional
import           Kore.Attribute.Hook
import           Kore.Attribute.Injective
import           Kore.Attribute.Smthook
import           Kore.Attribute.Smtlib
import qualified Kore.Attribute.Sort.Concat as Sort
import qualified Kore.Attribute.Sort.Element as Sort
import qualified Kore.Attribute.Sort.Unit as Sort
import qualified Kore.Builtin.Set as Set
import           Kore.Domain.Builtin
import           Kore.Internal.TermLike

import Test.Kore

-- -------------------------------------------------------------
-- * Builtin symbols

-- | Make an unparameterized builtin symbol with the given name.
builtinSymbol :: Text -> SymbolOrAlias
builtinSymbol name =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId name
        , symbolOrAliasParams = []
        }

-- ** Bool

orBoolSymbol :: SymbolOrAlias
orBoolSymbol = builtinSymbol "orBool"

orElseBoolSymbol :: SymbolOrAlias
orElseBoolSymbol = builtinSymbol "orElseBool"

andBoolSymbol :: SymbolOrAlias
andBoolSymbol = builtinSymbol "andBool"

andThenBoolSymbol :: SymbolOrAlias
andThenBoolSymbol = builtinSymbol "andThenBool"

xorBoolSymbol :: SymbolOrAlias
xorBoolSymbol = builtinSymbol "xorBool"

neBoolSymbol :: SymbolOrAlias
neBoolSymbol = builtinSymbol "neBool"

eqBoolSymbol :: SymbolOrAlias
eqBoolSymbol = builtinSymbol "eqBool"

notBoolSymbol :: SymbolOrAlias
notBoolSymbol = builtinSymbol "notBool"

impliesBoolSymbol :: SymbolOrAlias
impliesBoolSymbol = builtinSymbol "impliesBool"

-- ** Int

gtIntSymbol :: SymbolOrAlias
gtIntSymbol = builtinSymbol "gtInt"

geIntSymbol :: SymbolOrAlias
geIntSymbol = builtinSymbol "geInt"

eqIntSymbol :: SymbolOrAlias
eqIntSymbol = builtinSymbol "eqInt"

leIntSymbol :: SymbolOrAlias
leIntSymbol = builtinSymbol "leInt"

ltIntSymbol :: SymbolOrAlias
ltIntSymbol = builtinSymbol "ltInt"

neIntSymbol :: SymbolOrAlias
neIntSymbol = builtinSymbol "neInt"

minIntSymbol :: SymbolOrAlias
minIntSymbol = builtinSymbol "minInt"

maxIntSymbol :: SymbolOrAlias
maxIntSymbol = builtinSymbol "maxInt"

addIntSymbol :: SymbolOrAlias
addIntSymbol = builtinSymbol "addInt"

subIntSymbol :: SymbolOrAlias
subIntSymbol = builtinSymbol "subInt"

mulIntSymbol :: SymbolOrAlias
mulIntSymbol = builtinSymbol "mulInt"

absIntSymbol :: SymbolOrAlias
absIntSymbol = builtinSymbol "absInt"

tdivIntSymbol :: SymbolOrAlias
tdivIntSymbol = builtinSymbol "tdivInt"

tmodIntSymbol :: SymbolOrAlias
tmodIntSymbol = builtinSymbol "tmodInt"

andIntSymbol :: SymbolOrAlias
andIntSymbol = builtinSymbol "andInt"

orIntSymbol :: SymbolOrAlias
orIntSymbol = builtinSymbol "orInt"

xorIntSymbol :: SymbolOrAlias
xorIntSymbol = builtinSymbol "xorInt"

notIntSymbol :: SymbolOrAlias
notIntSymbol = builtinSymbol "notInt"

shlIntSymbol :: SymbolOrAlias
shlIntSymbol = builtinSymbol "shlInt"

shrIntSymbol :: SymbolOrAlias
shrIntSymbol = builtinSymbol "shrInt"

powIntSymbol :: SymbolOrAlias
powIntSymbol = builtinSymbol "powInt"

powmodIntSymbol :: SymbolOrAlias
powmodIntSymbol = builtinSymbol "powmodInt"

log2IntSymbol :: SymbolOrAlias
log2IntSymbol = builtinSymbol "log2Int"

emodIntSymbol :: SymbolOrAlias
emodIntSymbol = builtinSymbol "emodInt"

-- an unhooked, uninterpreted function f : Int -> Int
dummyIntSymbol :: SymbolOrAlias
dummyIntSymbol = builtinSymbol "f"

-- ** KEQUAL

keqBoolSymbol :: SymbolOrAlias
keqBoolSymbol = builtinSymbol "keqBool"

kneqBoolSymbol :: SymbolOrAlias
kneqBoolSymbol = builtinSymbol "kneqBool"

kiteKSymbol :: SymbolOrAlias
kiteKSymbol = builtinSymbol "kiteK"

kseqSymbol :: SymbolOrAlias
kseqSymbol = builtinSymbol "kseq"

dotkSymbol :: SymbolOrAlias
dotkSymbol = builtinSymbol "dotk"

injSymbol :: Sort -> Sort -> SymbolOrAlias
injSymbol lSort rSort =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId "inj"
        , symbolOrAliasParams = [lSort, rSort]
        }

-- ** List

unitListSymbol :: SymbolOrAlias
unitListSymbol = builtinSymbol "unitList"

unitList2Symbol :: SymbolOrAlias
unitList2Symbol = builtinSymbol "unitList2"

elementListSymbol :: SymbolOrAlias
elementListSymbol = builtinSymbol "elementList"

elementList2Symbol :: SymbolOrAlias
elementList2Symbol = builtinSymbol "elementList2"

concatListSymbol :: SymbolOrAlias
concatListSymbol = builtinSymbol "concatList"

concatList2Symbol :: SymbolOrAlias
concatList2Symbol = builtinSymbol "concatList2"

getListSymbol :: SymbolOrAlias
getListSymbol = builtinSymbol "getList"

-- ** Map

unitMapSymbol :: SymbolOrAlias
unitMapSymbol = builtinSymbol "unitMap"

updateMapSymbol :: SymbolOrAlias
updateMapSymbol = builtinSymbol "updateMap"

lookupMapSymbol :: SymbolOrAlias
lookupMapSymbol = builtinSymbol "lookupMap"

elementMapSymbol :: SymbolOrAlias
elementMapSymbol = builtinSymbol "elementMap"

concatMapSymbol :: SymbolOrAlias
concatMapSymbol = builtinSymbol "concatMap"

inKeysMapSymbol :: SymbolOrAlias
inKeysMapSymbol = builtinSymbol "inKeysMap"

keysMapSymbol :: SymbolOrAlias
keysMapSymbol = builtinSymbol "keysMap"

removeMapSymbol :: SymbolOrAlias
removeMapSymbol = builtinSymbol "removeMap"

removeAllMapSymbol :: SymbolOrAlias
removeAllMapSymbol = builtinSymbol "removeAllMap"

unitMap :: TermLike Variable
unitMap = mkApp mapSort unitMapSymbol []

updateMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
updateMap map' key value =
    mkApp mapSort updateMapSymbol [map', key, value]

lookupMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
lookupMap map' key =
    mkApp intSort lookupMapSymbol [map', key]

elementMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
elementMap key value =
    mkApp mapSort elementMapSymbol [key, value]

concatMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
concatMap map1 map2 =
    mkApp mapSort concatMapSymbol [map1, map2]

inKeysMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
inKeysMap key map' =
    mkApp boolSort inKeysMapSymbol [key, map']

keysMap
    :: TermLike Variable
    -> TermLike Variable
keysMap map' =
    mkApp setSort keysMapSymbol [map']

removeMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
removeMap map' key =
    mkApp mapSort removeMapSymbol [map', key]

removeAllMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
removeAllMap map' set =
    mkApp mapSort removeAllMapSymbol [map', set]

-- ** Pair

pairSymbol :: Sort -> Sort -> SymbolOrAlias
pairSymbol lSort rSort =
    SymbolOrAlias
        { symbolOrAliasConstructor = testId "pair"
        , symbolOrAliasParams = [lSort, rSort]
        }

-- ** Set

unitSetSymbol :: SymbolOrAlias
unitSetSymbol = builtinSymbol "unitSet"

unitSet :: TermLike Variable
unitSet = mkApp setSort unitSetSymbol []

elementSetSymbol :: SymbolOrAlias
elementSetSymbol = builtinSymbol "elementSet"

concatSetSymbol :: SymbolOrAlias
concatSetSymbol = builtinSymbol "concatSet"

inSetSymbol :: SymbolOrAlias
inSetSymbol = builtinSymbol "inSet"

differenceSetSymbol :: SymbolOrAlias
differenceSetSymbol = builtinSymbol "differenceSet"

toListSetSymbol :: SymbolOrAlias
toListSetSymbol = builtinSymbol "toListSet"

sizeSetSymbol :: SymbolOrAlias
sizeSetSymbol = builtinSymbol "sizeSet"

intersectionSetSymbol :: SymbolOrAlias
intersectionSetSymbol = builtinSymbol "intersectionSet"

intersectionSet
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
intersectionSet set1 set2 =
    mkApp setSort intersectionSetSymbol [set1, set2]

-- ** String

ltStringSymbol :: SymbolOrAlias
ltStringSymbol = builtinSymbol "ltString"

concatStringSymbol :: SymbolOrAlias
concatStringSymbol = builtinSymbol "concatString"

substrStringSymbol :: SymbolOrAlias
substrStringSymbol = builtinSymbol "substrString"

lengthStringSymbol :: SymbolOrAlias
lengthStringSymbol = builtinSymbol "lengthString"

chrStringSymbol :: SymbolOrAlias
chrStringSymbol = builtinSymbol "chrString"

ordStringSymbol :: SymbolOrAlias
ordStringSymbol = builtinSymbol "ordString"

findStringSymbol :: SymbolOrAlias
findStringSymbol = builtinSymbol "findString"

string2BaseStringSymbol :: SymbolOrAlias
string2BaseStringSymbol = builtinSymbol "string2baseString"

string2IntStringSymbol :: SymbolOrAlias
string2IntStringSymbol = builtinSymbol "string2intString"

ecdsaRecoverSymbol :: SymbolOrAlias
ecdsaRecoverSymbol = builtinSymbol "ECDSARecover"

keccakSymbol :: SymbolOrAlias
keccakSymbol = builtinSymbol "KECCAK"

-- -------------------------------------------------------------
-- * Sorts

-- | Declare 'a sort' in a Kore module.
sortDecl :: Sort -> ParsedSentence
sortDecl sort =
    asSentence sentence
  where
    sentence :: ParsedSentenceSort
    sentence =
        SentenceSort
            { sentenceSortName =
                let SortActualSort SortActual { sortActualName } = sort
                in sortActualName
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes []
            }

-- | Declare a hooked sort.
hookedSortDecl
    :: Sort
    -- ^ declared sort
    -> [ParsedPattern]
    -- ^ declaration attributes
    -> ParsedSentence
hookedSortDecl sort attrs =
    (asSentence . SentenceHookedSort) sentence
  where
    sentence :: ParsedSentenceSort
    sentence =
        SentenceSort
            { sentenceSortName =
                let SortActualSort SortActual { sortActualName } = sort
                in sortActualName
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes attrs
            }

-- ** Bool

-- | A sort to hook to the builtin @BOOL.Bool@.
boolSort :: Sort
boolSort =
    SortActualSort SortActual
        { sortActualName = testId "Bool"
        , sortActualSorts = []
        }

-- | Declare 'boolSort' in a Kore module.
boolSortDecl :: ParsedSentence
boolSortDecl = hookedSortDecl boolSort [ hookAttribute "BOOL.Bool" ]

builtinBool :: Bool -> InternalBool
builtinBool builtinBoolValue =
    InternalBool
        { builtinBoolSort = boolSort
        , builtinBoolValue
        }

-- ** Int

-- | A sort to hook to the builtin @INT.Int@.
intSort :: Sort
intSort =
    SortActualSort SortActual
        { sortActualName = testId "Int"
        , sortActualSorts = []
        }

-- | Declare 'intSort' in a Kore module.
intSortDecl :: ParsedSentence
intSortDecl = hookedSortDecl intSort [ hookAttribute "INT.Int" ]

builtinInt :: Integer -> InternalInt
builtinInt builtinIntValue =
    InternalInt
        { builtinIntSort = intSort
        , builtinIntValue
        }

-- ** KEQUAL

kSort :: Sort
kSort =
    SortActualSort SortActual
        { sortActualName = testId "SortK"
        , sortActualSorts = []
        }

kItemSort :: Sort
kItemSort =
    SortActualSort SortActual
        { sortActualName = testId "SortKItem"
        , sortActualSorts = []
        }

idSort :: Sort
idSort =
    SortActualSort SortActual
        { sortActualName = testId "SortId"
        , sortActualSorts = []
        }


-- ** List

-- | A sort to hook to the builtin @LIST.List@.
listSort :: Sort
listSort =
    SortActualSort SortActual
        { sortActualName = testId "List"
        , sortActualSorts = []
        }

-- | Declare 'listSort' in a Kore module.
listSortDecl :: ParsedSentence
listSortDecl =
    hookedSortDecl
        listSort
        [ hookAttribute "LIST.List"
        , Sort.unitAttribute unitListSymbol
        , Sort.elementAttribute elementListSymbol
        , Sort.concatAttribute concatListSymbol
        ]

builtinList
    :: [TermLike Variable]
    -> InternalList (TermLike Variable)
builtinList children =
    InternalList
        { builtinListSort = listSort
        , builtinListUnit = unitListSymbol
        , builtinListElement = elementListSymbol
        , builtinListConcat = concatListSymbol
        , builtinListChild = Seq.fromList children
        }

-- | Another sort with the same hook
listSort2 :: Sort
listSort2 =
    SortActualSort SortActual
        { sortActualName = testId "List2"
        , sortActualSorts = []
        }

-- | Declare 'listSort' in a Kore module.
listSortDecl2 :: ParsedSentence
listSortDecl2 =
    hookedSortDecl
        listSort2
        [ hookAttribute "LIST.List"
        , Sort.unitAttribute unitList2Symbol
        , Sort.elementAttribute elementList2Symbol
        , Sort.concatAttribute concatList2Symbol
        ]

-- ** Map

-- | A sort to hook to the builtin @MAP.Map@.
mapSort :: Sort
mapSort =
    SortActualSort SortActual
        { sortActualName = testId "Map"
        , sortActualSorts = []
        }

-- | Declare 'mapSort' in a Kore module.
mapSortDecl :: ParsedSentence
mapSortDecl =
    hookedSortDecl
        mapSort
        [ hookAttribute "MAP.Map"
        , Sort.unitAttribute unitMapSymbol
        , Sort.elementAttribute elementMapSymbol
        , Sort.concatAttribute concatMapSymbol
        ]

builtinMap
    :: [(TermLike Concrete, TermLike Variable)]
    -> InternalMap (TermLike Concrete) (TermLike Variable)
builtinMap children =
    InternalMap
        { builtinMapSort = mapSort
        , builtinMapUnit = unitMapSymbol
        , builtinMapElement = elementMapSymbol
        , builtinMapConcat = concatMapSymbol
        , builtinMapChild = Map.fromList children
        }

-- ** Pair

pairSort :: Sort -> Sort -> Sort
pairSort lSort rSort =
    SortActualSort SortActual
        { sortActualName = testId "Pair"
        , sortActualSorts = [lSort, rSort]
        }

-- | Declare 'Pair' in a Kore module.
pairSortDecl :: ParsedSentence
pairSortDecl =
    asSentence decl
  where
    lSortVariable = SortVariable (testId "l")
    rSortVariable = SortVariable (testId "r")
    lSort = SortVariableSort lSortVariable
    rSort = SortVariableSort rSortVariable
    decl :: ParsedSentenceSort
    decl =
        SentenceSort
            { sentenceSortName =
                let SortActualSort SortActual { sortActualName } =
                        pairSort lSort rSort
                in sortActualName
            , sentenceSortParameters = [lSortVariable, rSortVariable]
            , sentenceSortAttributes = Attributes []
            }

-- ** Set

-- | A sort to hook to the builtin @SET.Set@.
setSort :: Sort
setSort =
    SortActualSort SortActual
        { sortActualName = testId "Set"
        , sortActualSorts = []
        }

-- | Declare 'setSort' in a Kore module.
setSortDecl :: ParsedSentence
setSortDecl =
    hookedSortDecl
        setSort
        [ hookAttribute "SET.Set"
        , Sort.unitAttribute unitSetSymbol
        , Sort.elementAttribute elementSetSymbol
        , Sort.concatAttribute concatSetSymbol
        ]

builtinSet
    :: [TermLike Concrete]
    -> InternalSet (TermLike Concrete)
builtinSet children =
    InternalSet
        { builtinSetSort = setSort
        , builtinSetUnit = unitSetSymbol
        , builtinSetElement = elementSetSymbol
        , builtinSetConcat = concatSetSymbol
        , builtinSetChild = Set.fromList children
        }

-- ** String

-- | A sort to hook to the builtin @STRING.String@.
stringSort :: Sort
stringSort =
    SortActualSort SortActual
        { sortActualName = testId "String"
        , sortActualSorts = []
        }

-- | Declare 'stringSort' in a Kore module.
stringSortDecl :: ParsedSentence
stringSortDecl =
    hookedSortDecl
        stringSort
        [ hookAttribute "STRING.String" ]

-- -------------------------------------------------------------
-- * Modules

-- | Declare a symbol hooked to the given builtin name.
symbolDecl
    :: SymbolOrAlias
    -- ^ symbol
    -> Sort
    -- ^ result sort
    -> [Sort]
    -- ^ argument sorts
    -> [ParsedPattern]
    -- ^ declaration attributes
    -> ParsedSentence
symbolDecl
    SymbolOrAlias { symbolOrAliasConstructor }
    sentenceSymbolResultSort
    sentenceSymbolSorts
    (Attributes -> sentenceSymbolAttributes)
  =
    asSentence sentence
  where
    sentence :: ParsedSentenceSymbol
    sentence =
        SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes
            }
    sentenceSymbolSymbol =
        Symbol
            { symbolConstructor = symbolOrAliasConstructor
            , symbolParams = []
            }

-- | Declare a symbol hooked to the given builtin name.
hookedSymbolDecl
    :: SymbolOrAlias
    -- ^ symbol
    -> Sort
    -- ^ result sort
    -> [Sort]
    -- ^ argument sorts
    -> [ParsedPattern]
    -- ^ declaration attributes
    -> ParsedSentence
hookedSymbolDecl
    SymbolOrAlias { symbolOrAliasConstructor }
    sentenceSymbolResultSort
    sentenceSymbolSorts
    (Attributes -> sentenceSymbolAttributes)
  =
    (asSentence . SentenceHookedSymbol) sentence
  where
    sentence :: ParsedSentenceSymbol
    sentence =
        SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes
            }
    sentenceSymbolSymbol =
        Symbol
            { symbolConstructor = symbolOrAliasConstructor
            , symbolParams = []
            }

-- | Declare a symbol with no hook.
unhookedSymbolDecl
    :: SymbolOrAlias
    -- ^ symbol
    -> Sort
    -- ^ result sort
    -> [Sort]
    -- ^ argument sorts
    -> [ParsedPattern]
    -- ^ declaration attributes
    -> ParsedSentence
unhookedSymbolDecl
    SymbolOrAlias { symbolOrAliasConstructor }
    sentenceSymbolResultSort
    sentenceSymbolSorts
    (Attributes -> sentenceSymbolAttributes)
  =
    asSentence sentence
  where
    sentence :: ParsedSentenceSymbol
    sentence =
        SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes
            }
    sentenceSymbolSymbol =
        Symbol
            { symbolConstructor = symbolOrAliasConstructor
            , symbolParams = []
            }

importParsedModule :: ModuleName -> ParsedSentence
importParsedModule moduleName =
    asSentence sentence
  where
    sentence :: ParsedSentenceImport
    sentence =
        SentenceImport
            { sentenceImportModuleName = moduleName
            , sentenceImportAttributes = Attributes []
            }

-- ** BOOL

boolModuleName :: ModuleName
boolModuleName = ModuleName "BOOL"

-- | Declare the @BOOL@ builtins.
boolModule :: ParsedModule
boolModule =
    Module
        { moduleName = boolModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ boolSortDecl
            , binarySymbolDecl orBoolSymbol
                [hookAttribute "BOOL.or", smthookAttribute "or"]
            , binarySymbolDecl orElseBoolSymbol
                [hookAttribute "BOOL.orElse"]
            , binarySymbolDecl andBoolSymbol
                [hookAttribute "BOOL.and", smthookAttribute "and"]
            , binarySymbolDecl andThenBoolSymbol
                [hookAttribute "BOOL.andThen"]
            , binarySymbolDecl xorBoolSymbol
                [hookAttribute "BOOL.xor", smthookAttribute "xor"]
            , binarySymbolDecl neBoolSymbol
                [hookAttribute "BOOL.ne", smthookAttribute "distinct"]
            , binarySymbolDecl eqBoolSymbol
                [hookAttribute "BOOL.eq", smthookAttribute "="]
            , binarySymbolDecl impliesBoolSymbol
                [hookAttribute "BOOL.implies", smthookAttribute "=>"]
            , hookedSymbolDecl notBoolSymbol boolSort [boolSort]
                [hookAttribute "BOOL.not", smthookAttribute "not"]
            ]
        }
  where
    binarySymbolDecl symbol attrs =
        hookedSymbolDecl symbol boolSort [boolSort, boolSort] attrs

-- ** INT

intModuleName :: ModuleName
intModuleName = ModuleName "INT"

-- | Declare the @INT@ builtins.
intModule :: ParsedModule
intModule =
    Module
        { moduleName = intModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importParsedModule boolModuleName
            , intSortDecl
            -- comparison symbols
            , comparisonSymbolDecl gtIntSymbol
                [hookAttribute "INT.gt", smthookAttribute ">"]
            , comparisonSymbolDecl geIntSymbol
                [hookAttribute "INT.ge", smthookAttribute ">="]
            , comparisonSymbolDecl eqIntSymbol
                [hookAttribute "INT.eq", smthookAttribute "="]
            , comparisonSymbolDecl leIntSymbol
                [hookAttribute "INT.le", smthookAttribute "<="]
            , comparisonSymbolDecl ltIntSymbol
                [hookAttribute "INT.lt", smthookAttribute "<"]
            , comparisonSymbolDecl neIntSymbol
                [hookAttribute "INT.ne", smthookAttribute "distinct"]

            , binarySymbolDecl minIntSymbol
                [hookAttribute "INT.min", smtlibAttribute "int_min"]
            , binarySymbolDecl maxIntSymbol
                [hookAttribute "INT.max", smtlibAttribute "int_max"]
            , binarySymbolDecl addIntSymbol
                [hookAttribute "INT.add", smthookAttribute "+"]
            , binarySymbolDecl subIntSymbol
                [hookAttribute "INT.sub", smthookAttribute "-"]
            , binarySymbolDecl mulIntSymbol
                [hookAttribute "INT.mul", smthookAttribute "*"]
            , unarySymbolDecl absIntSymbol
                [ hookAttribute "INT.abs", smtlibAttribute "int_abs"
                , functionalAttribute]
            , binarySymbolDecl tdivIntSymbol
                [hookAttribute "INT.tdiv", smthookAttribute "div"]
            , binarySymbolDecl tmodIntSymbol
                [hookAttribute "INT.tmod", smthookAttribute "mod"]
            , binarySymbolDecl emodIntSymbol
                [hookAttribute "INT.emod", smthookAttribute "mod"]
            , unhookedUnarySymbolDecl dummyIntSymbol
                []
            , binarySymbolDecl andIntSymbol
                [hookAttribute "INT.and"]
            , binarySymbolDecl orIntSymbol
                [hookAttribute "INT.or"]
            , binarySymbolDecl xorIntSymbol
                [hookAttribute "INT.xor"]
            , unarySymbolDecl notIntSymbol
                [hookAttribute "INT.not"]
            , binarySymbolDecl shlIntSymbol
                [hookAttribute "INT.shl"]
            , binarySymbolDecl shrIntSymbol
                [hookAttribute "INT.shr"]
            , binarySymbolDecl powIntSymbol
                [hookAttribute "INT.pow"]
            , hookedSymbolDecl
                powmodIntSymbol
                intSort
                [intSort, intSort, intSort]
                [hookAttribute "INT.powmod"]
            , unarySymbolDecl log2IntSymbol
                [hookAttribute "INT.log2"]
            ]
        }
  where
    comparisonSymbolDecl symbol =
        hookedSymbolDecl symbol boolSort [intSort, intSort]

    unarySymbolDecl symbol =
        hookedSymbolDecl symbol intSort [intSort]

    binarySymbolDecl symbol =
        hookedSymbolDecl symbol intSort [intSort, intSort]

    unhookedUnarySymbolDecl symbol =
        unhookedSymbolDecl symbol intSort [intSort]

-- ** KEQUAL

kEqualModuleName :: ModuleName
kEqualModuleName = ModuleName "KEQUAL"

-- | Declare the @KEQUAL@ builtins.
kEqualModule :: ParsedModule
kEqualModule =
    Module
        { moduleName = kEqualModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importParsedModule boolModuleName
            , hookedSymbolDecl
                keqBoolSymbol
                boolSort
                [boolSort, boolSort]
                [hookAttribute "KEQUAL.eq"]
            , hookedSymbolDecl
                kneqBoolSymbol
                boolSort
                [boolSort, boolSort]
                [hookAttribute "KEQUAL.neq"]
            , hookedSymbolDecl
                kiteKSymbol
                kSort
                [boolSort, kSort, kSort]
                [hookAttribute "KEQUAL.ite"]
            , sortDecl kSort
            , sortDecl kItemSort
            , sortDecl idSort
            , symbolDecl kseqSymbol kSort [kSort, kSort] []
            , symbolDecl dotkSymbol kSort [] []
            , injSymbolDecl
            ]
        }

injSymbolDecl :: ParsedSentence
injSymbolDecl =
    asSentence decl
  where
    decl :: ParsedSentenceSymbol
    decl =
        SentenceSymbol
            { sentenceSymbolSymbol =
                Symbol
                    { symbolConstructor =
                        let SymbolOrAlias { symbolOrAliasConstructor } =
                                injSymbol fromSort toSort
                        in symbolOrAliasConstructor
                    , symbolParams = [fromSortVariable, toSortVariable]
                    }
            , sentenceSymbolSorts = [fromSort, toSort]
            , sentenceSymbolResultSort = toSort
            , sentenceSymbolAttributes =
                Attributes
                    [ constructorAttribute
                    , injectiveAttribute
                    ]
            }
    fromSortVariable = SortVariable (testId "from")
    toSortVariable = SortVariable (testId "to")
    fromSort = SortVariableSort fromSortVariable
    toSort = SortVariableSort toSortVariable

-- ** LIST

listModuleName :: ModuleName
listModuleName = ModuleName "LIST"

-- | Declare the @LIST@ builtins.
listModule :: ParsedModule
listModule =
    Module
        { moduleName = listModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importParsedModule intModuleName
            , listSortDecl
            , hookedSymbolDecl
                unitListSymbol
                listSort
                []
                [hookAttribute "LIST.unit"]
            , hookedSymbolDecl
                elementListSymbol
                listSort
                [intSort]
                [ hookAttribute "LIST.element"
                , functionalAttribute
                ]
            , hookedSymbolDecl
                concatListSymbol
                listSort
                [listSort, listSort]
                [ hookAttribute "LIST.concat"
                , functionalAttribute
                ]
            , hookedSymbolDecl
                getListSymbol
                intSort
                [listSort, intSort]
                [hookAttribute "LIST.get"]
            -- A second builtin List sort, to confuse 'asPattern'.
            , listSortDecl2
            , hookedSymbolDecl
                unitList2Symbol
                listSort2
                []
                [hookAttribute "LIST.unit"]
            , hookedSymbolDecl
                elementList2Symbol
                listSort2
                [intSort]
                [ hookAttribute "LIST.element"
                , functionalAttribute
                ]
            , hookedSymbolDecl
                concatList2Symbol
                listSort2
                [listSort2, listSort2]
                [ hookAttribute "LIST.concat"
                , functionalAttribute
                ]
            ]
        }

-- ** MAP

mapModuleName :: ModuleName
mapModuleName = ModuleName "MAP"

-- | Declare the @MAP@ builtins.
mapModule :: ParsedModule
mapModule =
    Module
        { moduleName = mapModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importParsedModule boolModuleName
            , importParsedModule intModuleName
            , importParsedModule setModuleName
            , mapSortDecl
            , hookedSymbolDecl
                unitMapSymbol
                mapSort
                []
                [hookAttribute "MAP.unit"]
            , hookedSymbolDecl
                (builtinSymbol "elementMap")
                mapSort
                [intSort, intSort]
                [ hookAttribute "MAP.element"
                , functionalAttribute
                ]
            , hookedSymbolDecl
                concatMapSymbol
                mapSort
                [mapSort, mapSort]
                [ hookAttribute "MAP.concat"
                , functionalAttribute
                ]
            , hookedSymbolDecl
                lookupMapSymbol
                intSort
                [mapSort, intSort]
                [hookAttribute "MAP.lookup"]
            , hookedSymbolDecl
                updateMapSymbol
                mapSort
                [mapSort, intSort, intSort]
                [hookAttribute "MAP.update"]
            , hookedSymbolDecl
                inKeysMapSymbol
                boolSort
                [intSort, mapSort]
                [hookAttribute "MAP.in_keys"]
            , hookedSymbolDecl
                keysMapSymbol
                setSort
                [mapSort]
                [hookAttribute "MAP.keys"]
            , hookedSymbolDecl
                removeMapSymbol
                mapSort
                [mapSort, intSort]
                [hookAttribute "MAP.remove"]
            , hookedSymbolDecl
                removeAllMapSymbol
                mapSort
                [mapSort, setSort]
                [hookAttribute "MAP.removeAll"]
            ]
        }

-- ** PAIR

pairModuleName :: ModuleName
pairModuleName = ModuleName "PAIR"

{- | Declare the @Pair@ sort and constructors.
 -}
pairModule :: ParsedModule
pairModule =
    Module
        { moduleName = pairModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ pairSortDecl
            , pairSymbolDecl
            ]
        }

pairSymbolDecl :: ParsedSentence
pairSymbolDecl =
    asSentence decl
  where
    decl :: ParsedSentenceSymbol
    decl =
        SentenceSymbol
            { sentenceSymbolSymbol =
                Symbol
                    { symbolConstructor =
                        let SymbolOrAlias { symbolOrAliasConstructor } =
                                pairSymbol leftSort rightSort
                        in symbolOrAliasConstructor
                    , symbolParams = [leftSortVariable, rightSortVariable]
                    }
            , sentenceSymbolSorts = [leftSort, rightSort]
            , sentenceSymbolResultSort = rightSort
            , sentenceSymbolAttributes =
                Attributes
                    [ constructorAttribute
                    , injectiveAttribute
                    , functionalAttribute
                    ]
            }
    leftSortVariable = SortVariable (testId "left")
    rightSortVariable = SortVariable (testId "right")
    leftSort = SortVariableSort leftSortVariable
    rightSort = SortVariableSort rightSortVariable

-- ** SET

setModuleName :: ModuleName
setModuleName = ModuleName "SET"

-- | Declare the @SET@ builtins.
setModule :: ParsedModule
setModule =
    Module
        { moduleName = setModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importParsedModule intModuleName
            , importParsedModule boolModuleName
            , importParsedModule listModuleName
            , setSortDecl
            , hookedSymbolDecl
                unitSetSymbol
                setSort
                []
                [hookAttribute Set.unitKey]
            , hookedSymbolDecl
                elementSetSymbol
                setSort
                [intSort]
                [ hookAttribute Set.elementKey
                , functionalAttribute
                ]
            , hookedSymbolDecl
                concatSetSymbol
                setSort
                [setSort, setSort]
                [ hookAttribute Set.concatKey
                , functionalAttribute
                ]
            , hookedSymbolDecl
                inSetSymbol
                boolSort
                [intSort, setSort]
                [hookAttribute Set.inKey]
            , hookedSymbolDecl
                differenceSetSymbol
                setSort
                [setSort, setSort]
                [hookAttribute Set.differenceKey]
            , hookedSymbolDecl
                toListSetSymbol
                listSort
                [setSort]
                [hookAttribute Set.toListKey]
            , hookedSymbolDecl
                sizeSetSymbol
                intSort
                [setSort]
                [hookAttribute Set.sizeKey]
            , hookedSymbolDecl
                intersectionSetSymbol
                setSort
                [setSort, setSort]
                [hookAttribute Set.intersectionKey]
            ]
        }

-- ** STRING

stringModuleName :: ModuleName
stringModuleName = ModuleName "STRING"

-- | Declare the @STRING@ builtins.
stringModule :: ParsedModule
stringModule =
    Module
        { moduleName = stringModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importParsedModule boolModuleName
            , importParsedModule intModuleName
            , stringSortDecl
            , hookedSymbolDecl
                ltStringSymbol
                boolSort
                [stringSort, stringSort]
                [hookAttribute "STRING.lt"]
            , hookedSymbolDecl
                concatStringSymbol
                stringSort
                [stringSort, stringSort]
                [hookAttribute "STRING.concat"]
            , hookedSymbolDecl
                substrStringSymbol
                stringSort
                [stringSort, intSort, intSort]
                [hookAttribute "STRING.substr"]
            , hookedSymbolDecl
                lengthStringSymbol
                intSort
                [stringSort]
                [hookAttribute "STRING.length"]
            , hookedSymbolDecl
                chrStringSymbol
                stringSort
                [intSort]
                [hookAttribute "STRING.chr"]
            , hookedSymbolDecl
                ordStringSymbol
                intSort
                [stringSort]
                [hookAttribute "STRING.ord"]
            , hookedSymbolDecl
                findStringSymbol
                intSort
                [stringSort, stringSort, intSort]
                [hookAttribute "STRING.find"]
            , hookedSymbolDecl
                string2BaseStringSymbol
                intSort
                [stringSort, intSort]
                [hookAttribute "STRING.string2base"]
            , hookedSymbolDecl
                string2IntStringSymbol
                intSort
                [stringSort]
                [hookAttribute "STRING.string2int"]
            ]
        }

-- ** KRYPTO

kryptoModuleName :: ModuleName
kryptoModuleName = ModuleName "KRYPTO"

-- | Declare the @KRYPTO@ builtins.
kryptoModule :: ParsedModule
kryptoModule =
    Module
        { moduleName = kryptoModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importParsedModule stringModuleName
            , importParsedModule intModuleName
            , importParsedModule listModuleName
            , hookedSymbolDecl
                ecdsaRecoverSymbol
                stringSort
                [stringSort, intSort, stringSort, stringSort]
                [hookAttribute "KRYPTO.ecdsaRecover"]
            , hookedSymbolDecl
                keccakSymbol
                stringSort
                [stringSort]
                [hookAttribute "KRYPTO.keccak256"]
            ]
        }

-- ** TEST

testModuleName :: ModuleName
testModuleName = ModuleName "TEST"

testModule :: ParsedModule
testModule =
    Module
        { moduleName = testModuleName
        , moduleAttributes = Attributes []
        , moduleSentences =
            [ importParsedModule boolModuleName
            , importParsedModule intModuleName
            , importParsedModule kEqualModuleName
            , importParsedModule listModuleName
            , importParsedModule mapModuleName
            , importParsedModule pairModuleName
            , importParsedModule setModuleName
            , importParsedModule stringModuleName
            , importParsedModule kryptoModuleName
            ]
        }

-- -------------------------------------------------------------
-- * Definition

testDefinition :: ParsedDefinition
testDefinition =
    Definition
        { definitionAttributes = Attributes []
        , definitionModules =
            [ boolModule
            , intModule
            , kEqualModule
            , listModule
            , mapModule
            , pairModule
            , setModule
            , stringModule
            , kryptoModule
            , testModule
            ]
        }
