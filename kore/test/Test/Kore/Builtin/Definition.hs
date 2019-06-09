module Test.Kore.Builtin.Definition where

import qualified Control.Lens as Lens
import qualified Data.Default as Default
import           Data.Function
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import           Data.Text
                 ( Text )

import           Kore.Attribute.Constructor
import           Kore.Attribute.Functional
import           Kore.Attribute.Hook
import           Kore.Attribute.Injective
import           Kore.Attribute.Parser
import           Kore.Attribute.Smthook
import qualified Kore.Attribute.Sort.Concat as Sort
import qualified Kore.Attribute.Sort.Element as Sort
import qualified Kore.Attribute.Sort.Unit as Sort
import           Kore.Attribute.SortInjection
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.Domain.Builtin
import qualified Kore.Internal.Symbol as Internal
import           Kore.Internal.TermLike hiding
                 ( Symbol )
import           Kore.Syntax.Definition as Syntax

import Test.Kore

-- -------------------------------------------------------------
-- * Builtin symbols

-- | Make an unparameterized builtin symbol with the given name.
builtinSymbol :: Text -> Internal.Symbol
builtinSymbol name =
    Internal.Symbol
        { symbolConstructor = testId name
        , symbolParams = []
        , symbolAttributes = Default.def
        }

-- ** Bool

orBoolSymbol :: Internal.Symbol
orBoolSymbol = builtinSymbol "orBool" & hook "BOOL.or" & smthook "or"

orElseBoolSymbol :: Internal.Symbol
orElseBoolSymbol = builtinSymbol "orElseBool" & hook "BOOL.orElse"

andBoolSymbol :: Internal.Symbol
andBoolSymbol = builtinSymbol "andBool" & hook "BOOL.and" & smthook "and"

andThenBoolSymbol :: Internal.Symbol
andThenBoolSymbol = builtinSymbol "andThenBool" & hook "BOOL.andThen"

xorBoolSymbol :: Internal.Symbol
xorBoolSymbol = builtinSymbol "xorBool" & hook "BOOL.xor" & smthook "xor"

neBoolSymbol :: Internal.Symbol
neBoolSymbol = builtinSymbol "neBool" & hook "BOOL.ne" & smthook "distinct"

eqBoolSymbol :: Internal.Symbol
eqBoolSymbol = builtinSymbol "eqBool" & hook "BOOL.eq" & smthook "="

notBoolSymbol :: Internal.Symbol
notBoolSymbol = builtinSymbol "notBool" & hook "BOOL.not" & smthook "not"

impliesBoolSymbol :: Internal.Symbol
impliesBoolSymbol =
    builtinSymbol "impliesBool" & hook "BOOL.implies" & smthook "=>"

-- ** Int

gtIntSymbol :: Internal.Symbol
gtIntSymbol = builtinSymbol "gtInt" & hook "INT.gt" & smthook ">"

geIntSymbol :: Internal.Symbol
geIntSymbol = builtinSymbol "geInt" & hook "INT.ge" & smthook ">="

eqIntSymbol :: Internal.Symbol
eqIntSymbol = builtinSymbol "eqInt" & hook "INT.eq" & smthook "="

leIntSymbol :: Internal.Symbol
leIntSymbol = builtinSymbol "leInt" & hook "INT.le" & smthook "<="

ltIntSymbol :: Internal.Symbol
ltIntSymbol = builtinSymbol "ltInt" & hook "INT.lt" & smthook "<"

neIntSymbol :: Internal.Symbol
neIntSymbol = builtinSymbol "neInt" & hook "INT.ne" & smthook "distinct"

minIntSymbol :: Internal.Symbol
minIntSymbol = builtinSymbol "minInt" & hook "INT.min" & smthook "int_min"

maxIntSymbol :: Internal.Symbol
maxIntSymbol = builtinSymbol "maxInt" & hook "INT.max" & smthook "int_max"

addIntSymbol :: Internal.Symbol
addIntSymbol = builtinSymbol "addInt" & hook "INT.add" & smthook "+"

subIntSymbol :: Internal.Symbol
subIntSymbol = builtinSymbol "subInt" & hook "INT.sub" & smthook "-"

mulIntSymbol :: Internal.Symbol
mulIntSymbol = builtinSymbol "mulInt" & hook "INT.mul" & smthook "*"

absIntSymbol :: Internal.Symbol
absIntSymbol =
    builtinSymbol "absInt" & functional & hook "INT.abs" & smthook "int_abs"

tdivIntSymbol :: Internal.Symbol
tdivIntSymbol = builtinSymbol "tdivInt" & hook "INT.tdiv" & smthook "div"

tmodIntSymbol :: Internal.Symbol
tmodIntSymbol = builtinSymbol "tmodInt" & hook "INT.tmod" & smthook "mod"

andIntSymbol :: Internal.Symbol
andIntSymbol = builtinSymbol "andInt" & hook "INT.and"

orIntSymbol :: Internal.Symbol
orIntSymbol = builtinSymbol "orInt" & hook "INT.or"

xorIntSymbol :: Internal.Symbol
xorIntSymbol = builtinSymbol "xorInt" & hook "INT.xor"

notIntSymbol :: Internal.Symbol
notIntSymbol = builtinSymbol "notInt" & hook "INT.not"

shlIntSymbol :: Internal.Symbol
shlIntSymbol = builtinSymbol "shlInt" & hook "INT.shl"

shrIntSymbol :: Internal.Symbol
shrIntSymbol = builtinSymbol "shrInt" & hook "INT.shr"

powIntSymbol :: Internal.Symbol
powIntSymbol = builtinSymbol "powInt" & hook "INT.pow"

powmodIntSymbol :: Internal.Symbol
powmodIntSymbol = builtinSymbol "powmodInt" & hook "INT.powmod"

log2IntSymbol :: Internal.Symbol
log2IntSymbol = builtinSymbol "log2Int" & hook "INT.log2"

emodIntSymbol :: Internal.Symbol
emodIntSymbol = builtinSymbol "emodInt" & hook "INT.emod" & smthook "mod"

-- an unhooked, uninterpreted function f : Int -> Int
dummyIntSymbol :: Internal.Symbol
dummyIntSymbol = builtinSymbol "f"

-- ** KEQUAL

keqBoolSymbol :: Internal.Symbol
keqBoolSymbol = builtinSymbol "keqBool" & hook "KEQUAL.eq"

kneqBoolSymbol :: Internal.Symbol
kneqBoolSymbol = builtinSymbol "kneqBool" & hook "KEQUAL.neq"

kiteKSymbol :: Internal.Symbol
kiteKSymbol = builtinSymbol "kiteK" & hook "KEQUAL.ite"

kseqSymbol :: Internal.Symbol
kseqSymbol = builtinSymbol "kseq"

dotkSymbol :: Internal.Symbol
dotkSymbol = builtinSymbol "dotk"

injSymbol :: Sort -> Sort -> Internal.Symbol
injSymbol lSort rSort =
    Internal.Symbol
        { symbolConstructor = testId "inj"
        , symbolParams = [lSort, rSort]
        , symbolAttributes =
            Default.def
                { Attribute.sortInjection = Attribute.SortInjection True }
        }

-- ** List

unitListSymbol :: Internal.Symbol
unitListSymbol = builtinSymbol "unitList" & hook "LIST.unit"

unitList2Symbol :: Internal.Symbol
unitList2Symbol = builtinSymbol "unitList2" & hook "LIST.unit"

elementListSymbol :: Internal.Symbol
elementListSymbol =
    builtinSymbol "elementList" & hook "LIST.element" & functional

elementList2Symbol :: Internal.Symbol
elementList2Symbol =
    builtinSymbol "elementList2" & hook "LIST.element" & functional

concatListSymbol :: Internal.Symbol
concatListSymbol = builtinSymbol "concatList" & hook "LIST.concat" & functional

concatList2Symbol :: Internal.Symbol
concatList2Symbol =
    builtinSymbol "concatList2" & hook "LIST.concat" & functional

getListSymbol :: Internal.Symbol
getListSymbol = builtinSymbol "getList" & hook "LIST.get"

-- ** Map

unitMapSymbol :: Internal.Symbol
unitMapSymbol = builtinSymbol "unitMap" & hook "MAP.unit"

updateMapSymbol :: Internal.Symbol
updateMapSymbol = builtinSymbol "updateMap" & hook "MAP.update"

lookupMapSymbol :: Internal.Symbol
lookupMapSymbol = builtinSymbol "lookupMap" & hook "MAP.lookup"

elementMapSymbol :: Internal.Symbol
elementMapSymbol = builtinSymbol "elementMap" & hook "MAP.element" & functional

concatMapSymbol :: Internal.Symbol
concatMapSymbol = builtinSymbol "concatMap" & hook "MAP.concat" & functional

inKeysMapSymbol :: Internal.Symbol
inKeysMapSymbol = builtinSymbol "inKeysMap" & hook "MAP.in_keys"

keysMapSymbol :: Internal.Symbol
keysMapSymbol = builtinSymbol "keysMap" & hook "MAP.keys"

removeMapSymbol :: Internal.Symbol
removeMapSymbol = builtinSymbol "removeMap" & hook "MAP.remove"

removeAllMapSymbol :: Internal.Symbol
removeAllMapSymbol = builtinSymbol "removeAllMap" & hook "MAP.removeAll"

unitMap :: TermLike Variable
unitMap = mkApplySymbol mapSort unitMapSymbol []

updateMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
updateMap map' key value =
    mkApplySymbol mapSort updateMapSymbol [map', key, value]

lookupMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
lookupMap map' key =
    mkApplySymbol intSort lookupMapSymbol [map', key]

elementMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
elementMap key value =
    mkApplySymbol mapSort elementMapSymbol [key, value]

concatMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
concatMap map1 map2 =
    mkApplySymbol mapSort concatMapSymbol [map1, map2]

inKeysMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
inKeysMap key map' =
    mkApplySymbol boolSort inKeysMapSymbol [key, map']

keysMap
    :: TermLike Variable
    -> TermLike Variable
keysMap map' =
    mkApplySymbol setSort keysMapSymbol [map']

removeMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
removeMap map' key =
    mkApplySymbol mapSort removeMapSymbol [map', key]

removeAllMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
removeAllMap map' set =
    mkApplySymbol mapSort removeAllMapSymbol [map', set]

smthook :: SExpr -> Internal.Symbol -> Internal.Symbol
smthook sExpr =
    Lens.set
        (Internal.lensSymbolAttributes . Attribute.lensSmthook)
        Attribute.Smthook { getSmthook = Just sExpr }

hook :: Text -> Internal.Symbol -> Internal.Symbol
hook name =
    Lens.set
        (Internal.lensSymbolAttributes . Attribute.lensHook)
        Attribute.Hook { getHook = Just name }

functional :: Internal.Symbol -> Internal.Symbol
functional =
    Lens.set
        (Internal.lensSymbolAttributes . Attribute.lensFunctional)
        Attribute.Functional { isDeclaredFunctional = True }

-- ** Pair

pairSymbol :: Sort -> Sort -> Internal.Symbol
pairSymbol lSort rSort =
    Internal.Symbol
        { symbolConstructor = testId "pair"
        , symbolParams = [lSort, rSort]
        , symbolAttributes = Default.def { Attribute.constructor = Attribute.Constructor True }
        }

-- ** Set

unitSetSymbol :: Internal.Symbol
unitSetSymbol = builtinSymbol "unitSet" & hook "SET.unit"

unitSet :: TermLike Variable
unitSet = mkApplySymbol setSort unitSetSymbol []

elementSetSymbol :: Internal.Symbol
elementSetSymbol = builtinSymbol "elementSet" & hook "SET.element" & functional

concatSetSymbol :: Internal.Symbol
concatSetSymbol = builtinSymbol "concatSet" & hook "SET.concat" & functional

inSetSymbol :: Internal.Symbol
inSetSymbol = builtinSymbol "inSet" & hook "SET.in"

differenceSetSymbol :: Internal.Symbol
differenceSetSymbol = builtinSymbol "differenceSet" & hook "SET.difference"

toListSetSymbol :: Internal.Symbol
toListSetSymbol = builtinSymbol "toListSet" & hook "SET.set2list"

sizeSetSymbol :: Internal.Symbol
sizeSetSymbol = builtinSymbol "sizeSet" & hook "SET.size"

intersectionSetSymbol :: Internal.Symbol
intersectionSetSymbol =
    builtinSymbol "intersectionSet" & hook "SET.intersection"

intersectionSet
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
intersectionSet set1 set2 =
    mkApplySymbol setSort intersectionSetSymbol [set1, set2]

-- ** String

ltStringSymbol :: Internal.Symbol
ltStringSymbol = builtinSymbol "ltString" & hook "STRING.lt"

concatStringSymbol :: Internal.Symbol
concatStringSymbol = builtinSymbol "concatString" & hook "STRING.concat"

substrStringSymbol :: Internal.Symbol
substrStringSymbol = builtinSymbol "substrString" & hook "STRING.substr"

lengthStringSymbol :: Internal.Symbol
lengthStringSymbol = builtinSymbol "lengthString" & hook "STRING.length"

chrStringSymbol :: Internal.Symbol
chrStringSymbol = builtinSymbol "chrString" & hook "STRING.chr"

ordStringSymbol :: Internal.Symbol
ordStringSymbol = builtinSymbol "ordString" & hook "STRING.ord"

findStringSymbol :: Internal.Symbol
findStringSymbol = builtinSymbol "findString" & hook "STRING.find"

string2BaseStringSymbol :: Internal.Symbol
string2BaseStringSymbol =
    builtinSymbol "string2baseString" & hook "STRING.string2base"

string2IntStringSymbol :: Internal.Symbol
string2IntStringSymbol =
    builtinSymbol "string2intString" & hook "STRING.string2int"

-- * Krypto

ecdsaRecoverSymbol :: Internal.Symbol
ecdsaRecoverSymbol =
    builtinSymbol "ecdsaRecoverKrypto" & hook "KRYPTO.ecdsaRecover"

keccakSymbol :: Internal.Symbol
keccakSymbol =
    builtinSymbol "keccak256Krypto" & hook "KRYPTO.keccak256"

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
        , unitAttribute unitListSymbol
        , elementAttribute elementListSymbol
        , concatAttribute concatListSymbol
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
        , unitAttribute unitList2Symbol
        , elementAttribute elementList2Symbol
        , concatAttribute concatList2Symbol
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
        , unitAttribute unitMapSymbol
        , elementAttribute elementMapSymbol
        , concatAttribute concatMapSymbol
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
        , unitAttribute unitSetSymbol
        , elementAttribute elementSetSymbol
        , concatAttribute concatSetSymbol
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

unitAttribute, elementAttribute, concatAttribute
    :: Internal.Symbol -> AttributePattern
unitAttribute = Sort.unitAttribute . Internal.toSymbolOrAlias
elementAttribute = Sort.elementAttribute . Internal.toSymbolOrAlias
concatAttribute = Sort.concatAttribute . Internal.toSymbolOrAlias

-- | Declare a symbol hooked to the given builtin name.
symbolDecl
    :: Internal.Symbol
    -- ^ symbol
    -> Sort
    -- ^ result sort
    -> [Sort]
    -- ^ argument sorts
    -> ParsedSentence
symbolDecl
    Internal.Symbol { symbolConstructor, symbolAttributes }
    sentenceSymbolResultSort
    sentenceSymbolSorts
  =
    asSentence sentence
  where
    sentence :: ParsedSentenceSymbol
    sentence =
        SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes = toAttributes symbolAttributes
            }
    sentenceSymbolSymbol =
        Symbol
            { symbolConstructor = symbolConstructor
            , symbolParams = []
            }

-- | Declare a symbol hooked to the given builtin name.
hookedSymbolDecl
    :: Internal.Symbol
    -- ^ symbol
    -> Sort
    -- ^ result sort
    -> [Sort]
    -- ^ argument sorts
    -> ParsedSentence
hookedSymbolDecl
    Internal.Symbol { symbolConstructor, symbolAttributes }
    sentenceSymbolResultSort
    sentenceSymbolSorts
  =
    (asSentence . SentenceHookedSymbol) sentence
  where
    sentence :: ParsedSentenceSymbol
    sentence =
        SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes = toAttributes symbolAttributes
            }
    sentenceSymbolSymbol =
        Symbol
            { symbolConstructor = symbolConstructor
            , symbolParams = []
            }

-- | Declare a symbol with no hook.
unhookedSymbolDecl
    :: Internal.Symbol
    -- ^ symbol
    -> Sort
    -- ^ result sort
    -> [Sort]
    -- ^ argument sorts
    -> ParsedSentence
unhookedSymbolDecl
    Internal.Symbol { symbolConstructor, symbolAttributes }
    sentenceSymbolResultSort
    sentenceSymbolSorts
  =
    asSentence sentence
  where
    sentence :: ParsedSentenceSymbol
    sentence =
        SentenceSymbol
            { sentenceSymbolSymbol
            , sentenceSymbolSorts
            , sentenceSymbolResultSort
            , sentenceSymbolAttributes = toAttributes symbolAttributes
            }
    sentenceSymbolSymbol =
        Symbol
            { symbolConstructor = symbolConstructor
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
            , binarySymbolDecl orElseBoolSymbol
            , binarySymbolDecl andBoolSymbol
            , binarySymbolDecl andThenBoolSymbol
            , binarySymbolDecl xorBoolSymbol
            , binarySymbolDecl neBoolSymbol
            , binarySymbolDecl eqBoolSymbol
            , binarySymbolDecl impliesBoolSymbol
            , hookedSymbolDecl notBoolSymbol boolSort [boolSort]
            ]
        }
  where
    binarySymbolDecl symbol =
        hookedSymbolDecl symbol boolSort [boolSort, boolSort]

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
            , comparisonSymbolDecl geIntSymbol
            , comparisonSymbolDecl eqIntSymbol
            , comparisonSymbolDecl leIntSymbol
            , comparisonSymbolDecl ltIntSymbol
            , comparisonSymbolDecl neIntSymbol

            , binarySymbolDecl minIntSymbol
            , binarySymbolDecl maxIntSymbol
            , binarySymbolDecl addIntSymbol
            , binarySymbolDecl subIntSymbol
            , binarySymbolDecl mulIntSymbol
            , unarySymbolDecl absIntSymbol
            , binarySymbolDecl tdivIntSymbol
            , binarySymbolDecl tmodIntSymbol
            , binarySymbolDecl emodIntSymbol
            , unhookedUnarySymbolDecl dummyIntSymbol
            , binarySymbolDecl andIntSymbol
            , binarySymbolDecl orIntSymbol
            , binarySymbolDecl xorIntSymbol
            , unarySymbolDecl notIntSymbol
            , binarySymbolDecl shlIntSymbol
            , binarySymbolDecl shrIntSymbol
            , binarySymbolDecl powIntSymbol
            , hookedSymbolDecl
                powmodIntSymbol
                intSort
                [intSort, intSort, intSort]
            , unarySymbolDecl log2IntSymbol
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
                [kSort, kSort]
            , hookedSymbolDecl
                kneqBoolSymbol
                boolSort
                [kSort, kSort]
            , hookedSymbolDecl
                kiteKSymbol
                kSort
                [boolSort, kSort, kSort]
            , sortDecl kSort
            , sortDecl kItemSort
            , sortDecl idSort
            , symbolDecl kseqSymbol kSort [kSort, kSort]
            , symbolDecl dotkSymbol kSort []
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
                        let Internal.Symbol { symbolConstructor } =
                                injSymbol fromSort toSort
                        in symbolConstructor
                    , symbolParams = [fromSortVariable, toSortVariable]
                    }
            , sentenceSymbolSorts = [fromSort, toSort]
            , sentenceSymbolResultSort = toSort
            , sentenceSymbolAttributes =
                Attributes
                    [ sortInjectionAttribute
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
            , hookedSymbolDecl
                elementListSymbol
                listSort
                [intSort]
            , hookedSymbolDecl
                concatListSymbol
                listSort
                [listSort, listSort]
            , hookedSymbolDecl
                getListSymbol
                intSort
                [listSort, intSort]
            -- A second builtin List sort, to confuse 'asPattern'.
            , listSortDecl2
            , hookedSymbolDecl
                unitList2Symbol
                listSort2
                []
            , hookedSymbolDecl
                elementList2Symbol
                listSort2
                [intSort]
            , hookedSymbolDecl
                concatList2Symbol
                listSort2
                [listSort2, listSort2]
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
            , hookedSymbolDecl unitMapSymbol mapSort []
            , hookedSymbolDecl elementMapSymbol mapSort [intSort, intSort]
            , hookedSymbolDecl concatMapSymbol mapSort [mapSort, mapSort]
            , hookedSymbolDecl lookupMapSymbol intSort [mapSort, intSort]
            , hookedSymbolDecl
                updateMapSymbol
                mapSort
                [mapSort, intSort, intSort]
            , hookedSymbolDecl inKeysMapSymbol boolSort [intSort, mapSort]
            , hookedSymbolDecl keysMapSymbol setSort [mapSort]
            , hookedSymbolDecl removeMapSymbol mapSort [mapSort, intSort]
            , hookedSymbolDecl removeAllMapSymbol mapSort [mapSort, setSort]
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
                        let Internal.Symbol { symbolConstructor } =
                                pairSymbol leftSort rightSort
                        in symbolConstructor
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
            , hookedSymbolDecl unitSetSymbol setSort []
            , hookedSymbolDecl elementSetSymbol setSort [intSort]
            , hookedSymbolDecl concatSetSymbol setSort [setSort, setSort]
            , hookedSymbolDecl inSetSymbol boolSort [intSort, setSort]
            , hookedSymbolDecl differenceSetSymbol setSort [setSort, setSort]
            , hookedSymbolDecl toListSetSymbol listSort [setSort]
            , hookedSymbolDecl sizeSetSymbol intSort [setSort]
            , hookedSymbolDecl intersectionSetSymbol setSort [setSort, setSort]
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
            , hookedSymbolDecl ltStringSymbol boolSort [stringSort, stringSort]
            , hookedSymbolDecl
                concatStringSymbol
                stringSort
                [stringSort, stringSort]
            , hookedSymbolDecl
                substrStringSymbol
                stringSort
                [stringSort, intSort, intSort]
            , hookedSymbolDecl lengthStringSymbol intSort [stringSort]
            , hookedSymbolDecl chrStringSymbol stringSort [intSort]
            , hookedSymbolDecl ordStringSymbol intSort [stringSort]
            , hookedSymbolDecl
                findStringSymbol
                intSort
                [stringSort, stringSort, intSort]
            , hookedSymbolDecl
                string2BaseStringSymbol
                intSort
                [stringSort, intSort]
            , hookedSymbolDecl string2IntStringSymbol intSort [stringSort]
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
            , hookedSymbolDecl keccakSymbol stringSort [stringSort]
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
