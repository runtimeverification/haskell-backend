module Test.Kore.Builtin.Definition where

import qualified Data.Bifunctor as Bifunctor
import qualified Data.Default as Default
import Data.Function
import qualified Data.Map.Strict as Map
import qualified Data.Sequence as Seq
import Data.Text
    ( Text
    )

import Kore.Attribute.Constructor
import Kore.Attribute.Functional
import Kore.Attribute.Hook
import Kore.Attribute.Injective
import Kore.Attribute.Parser
import qualified Kore.Attribute.Sort.Concat as Sort
import qualified Kore.Attribute.Sort.Element as Sort
import Kore.Attribute.Sort.HasDomainValues
    ( hasDomainValuesAttribute
    )
import qualified Kore.Attribute.Sort.Unit as Sort
import Kore.Attribute.SortInjection
import Kore.Domain.Builtin
import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.ApplicationSorts
import Kore.Internal.Symbol
    ( constructor
    , function
    , functional
    , hook
    , smthook
    , sortInjection
    )
import qualified Kore.Internal.Symbol as Internal
import Kore.Internal.TermLike hiding
    ( Symbol
    )
import Kore.Syntax.Definition as Syntax

import Test.Kore

-- -------------------------------------------------------------
-- * Builtin symbols

-- | Make an unparameterized builtin symbol with the given name.
builtinSymbol :: Text -> Sort -> [Sort] -> Internal.Symbol
builtinSymbol name resultSort operandSorts =
    Internal.Symbol
        { symbolConstructor = testId name
        , symbolParams = []
        , symbolAttributes = Default.def
        , symbolSorts = applicationSorts operandSorts resultSort
        }

unarySymbol :: Text -> Sort -> Internal.Symbol
unarySymbol name sort = builtinSymbol name sort [sort]

binarySymbol :: Text -> Sort -> Internal.Symbol
binarySymbol name sort = builtinSymbol name sort [sort, sort]

-- ** Bool

binaryBoolSymbol :: Text -> Internal.Symbol
binaryBoolSymbol name = binarySymbol name boolSort

orBoolSymbol :: Internal.Symbol
orBoolSymbol = binaryBoolSymbol "orBool" & hook "BOOL.or" & smthook "or"

orElseBoolSymbol :: Internal.Symbol
orElseBoolSymbol = binaryBoolSymbol "orElseBool" & hook "BOOL.orElse"

andBoolSymbol :: Internal.Symbol
andBoolSymbol = binaryBoolSymbol "andBool" & hook "BOOL.and" & smthook "and"

andThenBoolSymbol :: Internal.Symbol
andThenBoolSymbol = binaryBoolSymbol "andThenBool" & hook "BOOL.andThen"

xorBoolSymbol :: Internal.Symbol
xorBoolSymbol = binaryBoolSymbol "xorBool" & hook "BOOL.xor" & smthook "xor"

neBoolSymbol :: Internal.Symbol
neBoolSymbol = binaryBoolSymbol "neBool" & hook "BOOL.ne" & smthook "distinct"

eqBoolSymbol :: Internal.Symbol
eqBoolSymbol = binaryBoolSymbol "eqBool" & hook "BOOL.eq" & smthook "="

notBoolSymbol :: Internal.Symbol
notBoolSymbol =
    unarySymbol "notBool" boolSort
    & hook "BOOL.not"
    & smthook "not"

impliesBoolSymbol :: Internal.Symbol
impliesBoolSymbol =
    binaryBoolSymbol "impliesBool"
    & hook "BOOL.implies" & smthook "=>"

notBool :: TermLike Variable -> TermLike Variable
notBool x = mkApplySymbol notBoolSymbol [x]

andBool, impliesBool, eqBool, orBool
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
andBool x y = mkApplySymbol andBoolSymbol [x, y]
impliesBool x y = mkApplySymbol impliesBoolSymbol [x, y]
eqBool x y = mkApplySymbol eqBoolSymbol [x, y]
orBool x y = mkApplySymbol orBoolSymbol [x, y]

-- ** Int

comparisonSymbol :: Text -> Sort -> Internal.Symbol
comparisonSymbol name sort = builtinSymbol name boolSort [sort, sort]

comparisonIntSymbol :: Text -> Internal.Symbol
comparisonIntSymbol name = comparisonSymbol name intSort

unaryIntSymbol :: Text -> Internal.Symbol
unaryIntSymbol name = unarySymbol name intSort

binaryIntSymbol :: Text -> Internal.Symbol
binaryIntSymbol name = binarySymbol name intSort

gtIntSymbol :: Internal.Symbol
gtIntSymbol =
    comparisonIntSymbol "gtInt"
    & hook "INT.gt" & smthook ">" & function & functional

geIntSymbol :: Internal.Symbol
geIntSymbol =
    comparisonIntSymbol "geInt"
    & hook "INT.ge" & smthook ">=" & function & functional

eqIntSymbol :: Internal.Symbol
eqIntSymbol =
    comparisonIntSymbol "eqInt"
    & hook "INT.eq" & smthook "=" & function & functional

leIntSymbol :: Internal.Symbol
leIntSymbol =
    comparisonIntSymbol "leInt"
    & hook "INT.le" & smthook "<=" & function & functional

ltIntSymbol :: Internal.Symbol
ltIntSymbol =
    comparisonIntSymbol "ltInt"
    & hook "INT.lt" & smthook "<" & function & functional

neIntSymbol :: Internal.Symbol
neIntSymbol =
    comparisonIntSymbol "neInt"
    & hook "INT.ne" & smthook "distinct" & function & functional

minIntSymbol :: Internal.Symbol
minIntSymbol =
    binaryIntSymbol "minInt"
    & hook "INT.min" & smthook "int_min" & function & functional

maxIntSymbol :: Internal.Symbol
maxIntSymbol =
    binaryIntSymbol "maxInt"
    & hook "INT.max" & smthook "int_max" & function & functional

addIntSymbol :: Internal.Symbol
addIntSymbol =
    binaryIntSymbol "addInt"
    & hook "INT.add" & smthook "+" & function & functional

subIntSymbol :: Internal.Symbol
subIntSymbol =
    binaryIntSymbol "subInt"
    & hook "INT.sub" & smthook "-" & function & functional

mulIntSymbol :: Internal.Symbol
mulIntSymbol =
    binaryIntSymbol "mulInt"
    & hook "INT.mul" & smthook "*" & function & functional

absIntSymbol :: Internal.Symbol
absIntSymbol =
    unaryIntSymbol "absInt"
    & hook "INT.abs" & smthook "int_abs" & function & functional

tdivIntSymbol :: Internal.Symbol
tdivIntSymbol =
    binaryIntSymbol "tdivInt"
    & hook "INT.tdiv" & smthook "div" & function

tmodIntSymbol :: Internal.Symbol
tmodIntSymbol =
    binaryIntSymbol "tmodInt"
    & hook "INT.tmod" & smthook "mod" & function

andIntSymbol :: Internal.Symbol
andIntSymbol = binaryIntSymbol "andInt" & hook "INT.and" & function & functional

orIntSymbol :: Internal.Symbol
orIntSymbol = binaryIntSymbol "orInt" & hook "INT.or" & function & functional

xorIntSymbol :: Internal.Symbol
xorIntSymbol = binaryIntSymbol "xorInt" & hook "INT.xor" & function & functional

notIntSymbol :: Internal.Symbol
notIntSymbol = unaryIntSymbol "notInt" & hook "INT.not" & function & functional

shlIntSymbol :: Internal.Symbol
shlIntSymbol = binaryIntSymbol "shlInt" & hook "INT.shl" & function & functional

shrIntSymbol :: Internal.Symbol
shrIntSymbol = binaryIntSymbol "shrInt" & hook "INT.shr" & function & functional

powIntSymbol :: Internal.Symbol
powIntSymbol = binaryIntSymbol "powInt" & hook "INT.pow" & function

powmodIntSymbol :: Internal.Symbol
powmodIntSymbol =
    builtinSymbol "powmodInt" intSort [intSort, intSort, intSort]
    & hook "INT.powmod" & function

log2IntSymbol :: Internal.Symbol
log2IntSymbol = unaryIntSymbol "log2Int" & hook "INT.log2" & function

emodIntSymbol :: Internal.Symbol
emodIntSymbol =
    binaryIntSymbol "emodInt"
    & hook "INT.emod" & smthook "mod" & function

-- an unhooked, uninterpreted function f : Int -> Int
dummyIntSymbol :: Internal.Symbol
dummyIntSymbol = unaryIntSymbol "f" & function

dummyInt :: TermLike Variable -> TermLike Variable
dummyInt x = mkApplySymbol dummyIntSymbol [x]

addInt, subInt, mulInt, divInt, tdivInt, tmodInt
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
addInt i j = mkApplySymbol addIntSymbol  [i, j]
subInt i j = mkApplySymbol subIntSymbol  [i, j]
mulInt i j = mkApplySymbol mulIntSymbol  [i, j]
divInt i j = mkApplySymbol tdivIntSymbol [i, j]
tdivInt i j = mkApplySymbol tdivIntSymbol [i, j]
tmodInt i j = mkApplySymbol tmodIntSymbol [i, j]

eqInt, ltInt
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
eqInt i j = mkApplySymbol eqIntSymbol [i, j]
ltInt i j = mkApplySymbol ltIntSymbol [i, j]

-- ** KEQUAL

comparisonKSymbol :: Text -> Internal.Symbol
comparisonKSymbol name = comparisonSymbol name kSort

keqBoolSymbol :: Internal.Symbol
keqBoolSymbol = comparisonKSymbol "keqBool" & hook "KEQUAL.eq"

kneqBoolSymbol :: Internal.Symbol
kneqBoolSymbol = comparisonKSymbol "kneqBool" & hook "KEQUAL.neq"

kiteKSymbol :: Internal.Symbol
kiteKSymbol =
    builtinSymbol "kiteK" kSort [boolSort, kSort, kSort]
    & hook "KEQUAL.ite"

kseqSymbol :: Internal.Symbol
kseqSymbol =
    builtinSymbol "kseq" kSort [kItemSort, kSort]
    & constructor

dotkSymbol :: Internal.Symbol
dotkSymbol = builtinSymbol "dotk" kSort [] & constructor

injSymbol :: Sort -> Sort -> Internal.Symbol
injSymbol lSort rSort =
    Internal.Symbol
        { symbolConstructor = testId "inj"
        , symbolParams = [lSort, rSort]
        , symbolAttributes = Default.def
        , symbolSorts = applicationSorts [lSort] rSort
        }
    & sortInjection

inj :: Sort -> TermLike Variable -> TermLike Variable
inj toSort termLike =
    mkApplySymbol (injSymbol fromSort toSort) [termLike]
  where
    fromSort = termLikeSort termLike

keqBool, kneqBool
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
keqBool x y = mkApplySymbol keqBoolSymbol [x, y]
kneqBool x y = mkApplySymbol kneqBoolSymbol [x, y]

kseq :: TermLike Variable -> TermLike Variable -> TermLike Variable
kseq x y = mkApplySymbol kseqSymbol [x, y]

dotk :: TermLike Variable
dotk = mkApplySymbol dotkSymbol []

kiteK
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
kiteK i t e = mkApplySymbol kiteKSymbol [i, t, e]

-- ** List

unitListSymbol :: Internal.Symbol
unitListSymbol = builtinSymbol "unitList" listSort [] & hook "LIST.unit"

unitList2Symbol :: Internal.Symbol
unitList2Symbol = builtinSymbol "unitList2" listSort2 [] & hook "LIST.unit"

elementListSymbol :: Internal.Symbol
elementListSymbol =
    builtinSymbol "elementList" listSort [intSort]
    & hook "LIST.element" & functional

elementList2Symbol :: Internal.Symbol
elementList2Symbol =
    builtinSymbol "elementList2" listSort2 [intSort]
    & hook "LIST.element" & functional

concatListSymbol :: Internal.Symbol
concatListSymbol =
    binarySymbol "concatList" listSort & hook "LIST.concat" & functional

concatList2Symbol :: Internal.Symbol
concatList2Symbol =
    binarySymbol "concatList2" listSort2 & hook "LIST.concat" & functional

getListSymbol :: Internal.Symbol
getListSymbol =
    builtinSymbol "getList" intSort [listSort, intSort] & hook "LIST.get"

sizeListSymbol :: Internal.Symbol
sizeListSymbol = builtinSymbol "sizeList" intSort [listSort] & hook "LIST.size"

unitList :: TermLike Variable
unitList = mkApplySymbol unitListSymbol []

elementList :: TermLike Variable -> TermLike Variable
elementList x = mkApplySymbol elementListSymbol [x]

concatList :: TermLike Variable -> TermLike Variable -> TermLike Variable
concatList x y = mkApplySymbol concatListSymbol [x, y]

sizeList :: TermLike Variable -> TermLike Variable
sizeList l = mkApplySymbol sizeListSymbol [l]

-- ** Map

unitMapSymbol :: Internal.Symbol
unitMapSymbol = builtinSymbol "unitMap" mapSort [] & hook "MAP.unit"

updateMapSymbol :: Internal.Symbol
updateMapSymbol =
    builtinSymbol "updateMap" mapSort [mapSort, intSort, intSort]
    & hook "MAP.update"

lookupMapSymbol :: Internal.Symbol
lookupMapSymbol =
    builtinSymbol "lookupMap" intSort [mapSort, intSort]
    & hook "MAP.lookup"

elementMapSymbol :: Internal.Symbol
elementMapSymbol =
    builtinSymbol "elementMap" mapSort [intSort, intSort]
    & hook "MAP.element" & functional

concatMapSymbol :: Internal.Symbol
concatMapSymbol =
    binarySymbol "concatMap" mapSort & hook "MAP.concat" & functional

inKeysMapSymbol :: Internal.Symbol
inKeysMapSymbol =
    builtinSymbol "inKeysMap" boolSort [intSort, mapSort]
    & hook "MAP.in_keys"

keysMapSymbol :: Internal.Symbol
keysMapSymbol =
    builtinSymbol "keysMap" setSort [mapSort] & hook "MAP.keys"

removeMapSymbol :: Internal.Symbol
removeMapSymbol =
    builtinSymbol "removeMap" mapSort [mapSort, intSort] & hook "MAP.remove"

removeAllMapSymbol :: Internal.Symbol
removeAllMapSymbol =
    builtinSymbol "removeAllMap" mapSort [mapSort, setSort]
    & hook "MAP.removeAll"

sizeMapSymbol :: Internal.Symbol
sizeMapSymbol =
    builtinSymbol "sizeMap" intSort [mapSort] & hook "MAP.size"

unitMap :: TermLike Variable
unitMap = mkApplySymbol unitMapSymbol []

updateMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
updateMap map' key value = mkApplySymbol updateMapSymbol [map', key, value]

lookupMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
lookupMap map' key = mkApplySymbol lookupMapSymbol [map', key]

elementMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
elementMap key value = mkApplySymbol elementMapSymbol [key, value]

concatMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
concatMap map1 map2 = mkApplySymbol concatMapSymbol [map1, map2]

inKeysMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
inKeysMap key map' = mkApplySymbol inKeysMapSymbol [key, map']

keysMap
    :: TermLike Variable
    -> TermLike Variable
keysMap map' = mkApplySymbol keysMapSymbol [map']

removeMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
removeMap map' key = mkApplySymbol removeMapSymbol [map', key]

removeAllMap
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
removeAllMap map' set = mkApplySymbol removeAllMapSymbol [map', set]

sizeMap
    :: TermLike Variable
    -> TermLike Variable
sizeMap map' = mkApplySymbol sizeMapSymbol [map']

-- ** Pair

pairSymbol :: Sort -> Sort -> Internal.Symbol
pairSymbol lSort rSort =
    Internal.Symbol
        { symbolConstructor = testId "pair"
        , symbolParams = [lSort, rSort]
        , symbolAttributes = Default.def
        , symbolSorts = applicationSorts [lSort, rSort] (pairSort lSort rSort)
        }
    & constructor

pair :: TermLike Variable -> TermLike Variable -> TermLike Variable
pair l r =
    mkApplySymbol (pairSymbol lSort rSort) [l, r]
  where
    lSort = termLikeSort l
    rSort = termLikeSort r

-- ** Set

unitSetSymbol :: Internal.Symbol
unitSetSymbol = builtinSymbol "unitSet" setSort [] & hook "SET.unit"

unitSet :: TermLike Variable
unitSet = mkApplySymbol unitSetSymbol []

elementSetSymbol :: Internal.Symbol
elementSetSymbol =
    builtinSymbol "elementSet" setSort [intSort]
    & hook "SET.element" & functional

elementSet :: TermLike Variable -> TermLike Variable
elementSet x = mkApplySymbol elementSetSymbol [x]

concatSetSymbol :: Internal.Symbol
concatSetSymbol =
    binarySymbol "concatSet" setSort & hook "SET.concat" & functional

concatSet
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
concatSet s1 s2 = mkApplySymbol concatSetSymbol [s1, s2]

inSetSymbol :: Internal.Symbol
inSetSymbol =
    builtinSymbol "inSet" boolSort [intSort, setSort] & hook "SET.in"

differenceSetSymbol :: Internal.Symbol
differenceSetSymbol =
    binarySymbol "differenceSet" setSort & hook "SET.difference"

toListSetSymbol :: Internal.Symbol
toListSetSymbol =
    builtinSymbol "toListSet" listSort [setSort] & hook "SET.set2list"

sizeSetSymbol :: Internal.Symbol
sizeSetSymbol = builtinSymbol "sizeSet" intSort [setSort] & hook "SET.size"

intersectionSetSymbol :: Internal.Symbol
intersectionSetSymbol =
    binarySymbol "intersectionSet" setSort & hook "SET.intersection"

list2setSetSymbol :: Internal.Symbol
list2setSetSymbol =
    builtinSymbol "list2setSet" setSort [listSort] & hook "SET.list2set"

intersectionSet
    :: TermLike Variable
    -> TermLike Variable
    -> TermLike Variable
intersectionSet set1 set2 =
    mkApplySymbol intersectionSetSymbol [set1, set2]

list2setSet
    :: TermLike Variable
    -> TermLike Variable
list2setSet list =
    mkApplySymbol list2setSetSymbol [list]

-- ** String

ltStringSymbol :: Internal.Symbol
ltStringSymbol =
    comparisonSymbol "ltString" stringSort & hook "STRING.lt"

concatStringSymbol :: Internal.Symbol
concatStringSymbol =
    binarySymbol "concatString" stringSort & hook "STRING.concat"

substrStringSymbol :: Internal.Symbol
substrStringSymbol =
    builtinSymbol "substrString" stringSort [stringSort, intSort, intSort]
    & hook "STRING.substr"

lengthStringSymbol :: Internal.Symbol
lengthStringSymbol =
    builtinSymbol "lengthString" intSort [stringSort] & hook "STRING.length"

chrStringSymbol :: Internal.Symbol
chrStringSymbol =
    builtinSymbol "chrString" stringSort [intSort] & hook "STRING.chr"

ordStringSymbol :: Internal.Symbol
ordStringSymbol =
    builtinSymbol "ordString" intSort [stringSort] & hook "STRING.ord"

findStringSymbol :: Internal.Symbol
findStringSymbol =
    builtinSymbol "findString" intSort [stringSort, stringSort, intSort]
    & hook "STRING.find"

string2BaseStringSymbol :: Internal.Symbol
string2BaseStringSymbol =
    builtinSymbol "string2baseString" intSort [stringSort, intSort]
    & hook "STRING.string2base"

string2IntStringSymbol :: Internal.Symbol
string2IntStringSymbol =
    builtinSymbol "string2intString" intSort [stringSort]
    & hook "STRING.string2int"

token2StringStringSymbol :: Internal.Symbol
token2StringStringSymbol =
    builtinSymbol "token2stringString" stringSort [userTokenSort]
    & hook "STRING.token2string"

string2TokenStringSymbol :: Internal.Symbol
string2TokenStringSymbol =
    builtinSymbol "string2tokenString" userTokenSort [stringSort]
    & hook "STRING.string2token"

-- * Krypto

ecdsaRecoverSymbol :: Internal.Symbol
ecdsaRecoverSymbol =
    builtinSymbol
        "ecdsaRecoverKrypto"
        stringSort
        [stringSort, intSort, stringSort, stringSort]
    & hook "KRYPTO.ecdsaRecover"

keccakSymbol :: Internal.Symbol
keccakSymbol =
    builtinSymbol "keccak256Krypto" stringSort [stringSort]
    & hook "KRYPTO.keccak256"

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

sortDeclWithAttributes
    :: Sort
    -- ^ declared sort
    -> [ParsedPattern]
    -- ^ declaration attributes
    -> ParsedSentence
sortDeclWithAttributes sort attributes =
    asSentence sentence
  where
    sentence :: ParsedSentenceSort
    sentence =
        SentenceSort
            { sentenceSortName =
                let SortActualSort SortActual { sortActualName } = sort
                in sortActualName
            , sentenceSortParameters = []
            , sentenceSortAttributes = Attributes attributes
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
    InternalAc
        { builtinAcSort = mapSort
        , builtinAcUnit = unitMapSymbol
        , builtinAcElement = elementMapSymbol
        , builtinAcConcat = concatMapSymbol
        , builtinAcChild = Domain.NormalizedMap Domain.NormalizedAc
            { elementsWithVariables = []
            , concreteElements =
                Map.fromList (Bifunctor.second Domain.MapValue <$> children)
            , opaque = []
            }
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
    -> InternalSet (TermLike Concrete) (TermLike Variable)
builtinSet children =
    InternalAc
        { builtinAcSort = setSort
        , builtinAcUnit = unitSetSymbol
        , builtinAcElement = elementSetSymbol
        , builtinAcConcat = concatSetSymbol
        , builtinAcChild = Domain.NormalizedSet Domain.NormalizedAc
            { elementsWithVariables = []
            , concreteElements =
                Map.fromList (map (\x -> (x, SetValue)) children)
            , opaque = []
            }
        }

-- ** String

-- | A sort to hook to the builtin @STRING.String@.
stringSort :: Sort
stringSort =
    SortActualSort SortActual
        { sortActualName = testId "String"
        , sortActualSorts = []
        }

-- | A user defined token sort
userTokenSort :: Sort
userTokenSort =
    SortActualSort SortActual
        { sortActualName = testId "UserToken"
        , sortActualSorts = []
        }

-- | Declare 'stringSort' in a Kore module.
stringSortDecl :: ParsedSentence
stringSortDecl =
    hookedSortDecl
        stringSort
        [ hookAttribute "STRING.String" ]

-- | Declare a user defined token sort in a Kore module
userTokenSortDecl :: ParsedSentence
userTokenSortDecl =
    sortDeclWithAttributes
        userTokenSort
        [ hasDomainValuesAttribute ]

-- -------------------------------------------------------------
-- * Modules

unitAttribute, elementAttribute, concatAttribute
    :: Internal.Symbol -> AttributePattern
unitAttribute = Sort.unitAttribute . Internal.toSymbolOrAlias
elementAttribute = Sort.elementAttribute . Internal.toSymbolOrAlias
concatAttribute = Sort.concatAttribute . Internal.toSymbolOrAlias

-- | Declare a symbol hooked to the given builtin name.
hookedSymbolDecl :: Internal.Symbol -> ParsedSentence
hookedSymbolDecl symbol =
    (asSentence . SentenceHookedSymbol) sentence
  where
    Internal.Symbol { symbolConstructor, symbolAttributes, symbolSorts } =
        symbol
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
    sentenceSymbolSorts = applicationSortsOperands symbolSorts
    sentenceSymbolResultSort = applicationSortsResult symbolSorts

symbolDecl :: Internal.Symbol -> ParsedSentence
symbolDecl symbol =
    asSentence sentence
  where
    Internal.Symbol { symbolConstructor, symbolAttributes, symbolSorts } =
        symbol
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
    sentenceSymbolSorts = applicationSortsOperands symbolSorts
    sentenceSymbolResultSort = applicationSortsResult symbolSorts

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
            , hookedSymbolDecl orBoolSymbol
            , hookedSymbolDecl orElseBoolSymbol
            , hookedSymbolDecl andBoolSymbol
            , hookedSymbolDecl andThenBoolSymbol
            , hookedSymbolDecl xorBoolSymbol
            , hookedSymbolDecl neBoolSymbol
            , hookedSymbolDecl eqBoolSymbol
            , hookedSymbolDecl impliesBoolSymbol
            , hookedSymbolDecl notBoolSymbol
            ]
        }

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
            , hookedSymbolDecl gtIntSymbol
            , hookedSymbolDecl geIntSymbol
            , hookedSymbolDecl eqIntSymbol
            , hookedSymbolDecl leIntSymbol
            , hookedSymbolDecl ltIntSymbol
            , hookedSymbolDecl neIntSymbol

            , hookedSymbolDecl minIntSymbol
            , hookedSymbolDecl maxIntSymbol
            , hookedSymbolDecl addIntSymbol
            , hookedSymbolDecl subIntSymbol
            , hookedSymbolDecl mulIntSymbol
            , hookedSymbolDecl absIntSymbol
            , hookedSymbolDecl tdivIntSymbol
            , hookedSymbolDecl tmodIntSymbol
            , hookedSymbolDecl emodIntSymbol
            , symbolDecl dummyIntSymbol
            , hookedSymbolDecl andIntSymbol
            , hookedSymbolDecl orIntSymbol
            , hookedSymbolDecl xorIntSymbol
            , hookedSymbolDecl notIntSymbol
            , hookedSymbolDecl shlIntSymbol
            , hookedSymbolDecl shrIntSymbol
            , hookedSymbolDecl powIntSymbol
            , hookedSymbolDecl powmodIntSymbol
            , hookedSymbolDecl log2IntSymbol
            ]
        }

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
            , hookedSymbolDecl keqBoolSymbol
            , hookedSymbolDecl kneqBoolSymbol
            , hookedSymbolDecl kiteKSymbol
            , sortDecl kSort
            , sortDecl kItemSort
            , sortDecl idSort
            , symbolDecl kseqSymbol
            , symbolDecl dotkSymbol
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
            , hookedSymbolDecl unitListSymbol
            , hookedSymbolDecl elementListSymbol
            , hookedSymbolDecl concatListSymbol
            , hookedSymbolDecl getListSymbol
            -- A second builtin List sort, to confuse 'asPattern'.
            , listSortDecl2
            , hookedSymbolDecl unitList2Symbol
            , hookedSymbolDecl elementList2Symbol
            , hookedSymbolDecl concatList2Symbol
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
            , hookedSymbolDecl unitMapSymbol
            , hookedSymbolDecl elementMapSymbol
            , hookedSymbolDecl concatMapSymbol
            , hookedSymbolDecl lookupMapSymbol
            , hookedSymbolDecl updateMapSymbol
            , hookedSymbolDecl inKeysMapSymbol
            , hookedSymbolDecl keysMapSymbol
            , hookedSymbolDecl removeMapSymbol
            , hookedSymbolDecl removeAllMapSymbol
            , hookedSymbolDecl sizeMapSymbol
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
            , sentenceSymbolResultSort = pairSort leftSort rightSort
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
            , hookedSymbolDecl unitSetSymbol
            , hookedSymbolDecl elementSetSymbol
            , hookedSymbolDecl concatSetSymbol
            , hookedSymbolDecl inSetSymbol
            , hookedSymbolDecl differenceSetSymbol
            , hookedSymbolDecl toListSetSymbol
            , hookedSymbolDecl sizeSetSymbol
            , hookedSymbolDecl intersectionSetSymbol
            , hookedSymbolDecl list2setSetSymbol
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
            , userTokenSortDecl
            , hookedSymbolDecl ltStringSymbol
            , hookedSymbolDecl concatStringSymbol
            , hookedSymbolDecl substrStringSymbol
            , hookedSymbolDecl lengthStringSymbol
            , hookedSymbolDecl chrStringSymbol
            , hookedSymbolDecl ordStringSymbol
            , hookedSymbolDecl findStringSymbol
            , hookedSymbolDecl string2BaseStringSymbol
            , hookedSymbolDecl string2IntStringSymbol
            , hookedSymbolDecl token2StringStringSymbol
            , hookedSymbolDecl string2TokenStringSymbol
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
            , hookedSymbolDecl ecdsaRecoverSymbol
            , hookedSymbolDecl keccakSymbol
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
