{-# LANGUAGE QuasiQuotes #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Fixture (
    module Test.Booster.Fixture,
) where

import Data.ByteString.Char8 (ByteString)
import Data.Map qualified as Map
import Data.Set qualified as Set

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.Pattern.Base
import Booster.SMT.Base
import Booster.Syntax.Json.Internalise (trm)
import Booster.Syntax.ParsedKore.Internalise (symb)

mockUniqueId :: UniqueId
mockUniqueId = UniqueId "MOCK"

someSort, aSubsort, differentSort, kSort, kItemSort, listSort, setSort, boolSort :: Sort
someSort = SortApp "SomeSort" []
aSubsort = SortApp "AnotherSort" []
differentSort = SortApp "DifferentSort" []
kSort = SortApp "SortK" []
kItemSort = SortApp "SortKItem" []
listSort = SortApp testKListDef.listSortName []
setSort = SortApp testKSetDef.listSortName []
boolSort = SortApp "SortBool" []

testDefinition :: KoreDefinition
testDefinition =
    KoreDefinition
        { attributes = defaultDefAttributes
        , modules = Map.singleton "AMODULE" ModuleAttributes
        , sorts =
            Map.fromList
                [ someSort `withSubsorts` [aSubsort]
                , aSubsort `withSubsorts` []
                , differentSort `withSubsorts` []
                , kSort `withSubsorts` []
                , listSort `withSubsorts` []
                , setSort `withSubsorts` []
                , boolSort `withSubsorts` []
                ]
        , symbols =
            Map.fromList
                [ ("con1", con1)
                , ("con2", con2)
                , ("con3", con3)
                , ("con4", con4)
                , ("f1", f1)
                , ("f2", f2)
                , ("f3", f3)
                , ("g", g)
                , ("Lbl'UndsEqlsEqls'K'Und'", eqK)
                , ("kseq", kseq)
                , ("dotk", dotk)
                ]
                <> listSymbols
                <> setSymbols
        , rewriteTheory = Map.empty
        , functionEquations = Map.empty
        , simplifications = Map.empty
        , ceils = Map.empty
        }
  where
    super `withSubsorts` subs =
        ( getName super
        ,
            ( SortAttributes{argCount = 0, collectionAttributes = Nothing}
            , Set.fromList (getName super : map getName subs)
            )
        )
    -- sort variables and sort applications with arguments cause an error
    getName (SortApp n []) = n
    getName other = error $ "subSortOf: " <> show other <> " not supported"

var :: VarName -> Sort -> Term
var variableName variableSort = Var $ Variable{variableSort, variableName}

dv :: Sort -> ByteString -> Term
dv = DomainValue

app :: Symbol -> [Term] -> Term
app s = SymbolApplication s []

inj :: Sort -> Sort -> Term -> Term
inj = Injection

con1, con2, con3, con4, f1, f2, f3, g, eqK, kseq, dotk :: Symbol
con1 = [symb| symbol con1{}(SomeSort{}) : SomeSort{} [constructor{}()] |]
con2 = [symb| symbol con2{}(SomeSort{}) : SomeSort{} [constructor{}()] |]
con3 = [symb| symbol con3{}(SomeSort{}, SomeSort{}) : SomeSort{} [constructor{}()] |]
con4 = [symb| symbol con4{}(SomeSort{}, SomeSort{}) : AnotherSort{} [constructor{}()] |]
f1 = [symb| symbol f1{}(SomeSort{}) : SomeSort{} [function{}(), total{}()] |]
f2 = [symb| symbol f2{}(SomeSort{}) : SomeSort{} [function{}()] |]
f3 = [symb| symbol f3{}(SomeSort{}) : SortTestKMap{} [function{}()] |]
g = [symb| symbol g{}() : SortTestKMapKey{} [function{}(), total{}()] |]
eqK =
    Symbol
        { name = "Lbl'UndsEqlsEqls'K'Unds'"
        , sortVars = []
        , argSorts = [SortApp "SortK" [], SortApp "SortK" []]
        , resultSort = SortApp "SortBool" []
        , attributes =
            SymbolAttributes
                { collectionMetadata = Nothing
                , symbolType = Function Total
                , isIdem = IsNotIdem
                , isAssoc = IsNotAssoc
                , isMacroOrAlias = IsNotMacroOrAlias
                , hasEvaluators = CanBeEvaluated
                , smt = Just (SMTHook (Atom "="))
                , hook = Just "KEQUAL.eq"
                }
        }
kseq = [symb| symbol kseq{}(SortKItem{}, SortK{}) : SortK{} [constructor{}()] |]
dotk = [symb| symbol dotk{}() : SortK{} [constructor{}()] |]

--------------------------------------------------------------------------------

testKMapDefinition :: KMapDefinition
testKMapDefinition =
    KMapDefinition
        { symbolNames = testKMapSymbolNames
        , keySortName = "SortTestKMapKey"
        , elementSortName = "SortTestKMapItem"
        , mapSortName = "SortTestKMap"
        }
  where
    testKMapSymbolNames =
        KCollectionSymbolNames
            { unitSymbolName = "Lbl'Stop'TestKMap"
            , elementSymbolName = "LblTestKMapItem"
            , concatSymbolName = "Lbl'Unds'TestKMap'Unds'"
            }

kmapKeySort, kmapElementSort, kmapSort :: Sort
kmapKeySort = SortApp testKMapDefinition.keySortName []
kmapElementSort = SortApp testKMapDefinition.elementSortName []
kmapSort = SortApp testKMapDefinition.mapSortName []

emptyKMap
    , concreteKMapWithOneItem
    , concreteKMapWithTwoItems
    , concreteKMapWithOneItemAndRest
    , concreteKeySymbolicValueKMapWithRest
    , symbolicKMapWithOneItem
    , symbolicKMapWithTwoItems
    , concreteAndSymbolicKMapWithTwoItems
    , functionKMapWithOneItemAndRest
    , functionKMapWithOneItem ::
        Term
emptyKMap = KMap testKMapDefinition [] Nothing
concreteKMapWithOneItem =
    KMap
        testKMapDefinition
        [
            ( [trm| \dv{SortTestKMapKey{}}("key") |]
            , [trm| \dv{SortTestKMapItem{}}("value") |]
            )
        ]
        Nothing
concreteKMapWithOneItemAndRest =
    KMap
        testKMapDefinition
        [
            ( [trm| \dv{SortTestKMapKey{}}("key") |]
            , [trm| \dv{SortTestKMapItem{}}("value") |]
            )
        ]
        (Just [trm| REST:SortTestKMap{}|])
concreteKeySymbolicValueKMapWithRest =
    KMap
        testKMapDefinition
        [
            ( [trm| \dv{SortTestKMapKey{}}("key") |]
            , [trm| A:SortTestKMapItem{} |]
            )
        ]
        (Just [trm| REST:SortTestKMap{}|])
concreteKMapWithTwoItems =
    KMap
        testKMapDefinition
        [
            ( [trm| \dv{SortTestKMapKey{}}("key") |]
            , [trm| \dv{SortTestKMapItem{}}("value") |]
            )
        ,
            ( [trm| \dv{SortTestKMapKey{}}("key2") |]
            , [trm| \dv{SortTestKMapItem{}}("value2") |]
            )
        ]
        Nothing
symbolicKMapWithOneItem =
    KMap
        testKMapDefinition
        [
            ( [trm| \dv{SortTestKMapKey{}}("key") |]
            , [trm| B:SortTestKMapItem{} |]
            )
        ]
        Nothing
symbolicKMapWithTwoItems =
    KMap
        testKMapDefinition
        [
            ( [trm| \dv{SortTestKMapKey{}}("key") |]
            , [trm| A:SortTestKMapItem{} |]
            )
        ,
            ( [trm| \dv{SortTestKMapKey{}}("key2") |]
            , [trm| B:SortTestKMapItem{} |]
            )
        ]
        Nothing
concreteAndSymbolicKMapWithTwoItems =
    KMap
        testKMapDefinition
        [
            ( [trm| \dv{SortTestKMapKey{}}("key") |]
            , [trm| \dv{SortTestKMapItem{}}("value") |]
            )
        ,
            ( [trm| A:SortTestKMapKey{}|]
            , [trm| \dv{SortTestKMapItem{}}("value2") |]
            )
        ]
        Nothing
functionKMapWithOneItemAndRest =
    KMap
        testKMapDefinition
        [
            ( [trm| g{}() |]
            , [trm| \dv{SortTestKMapItem{}}("value") |]
            )
        ]
        (Just [trm| REST:SortTestKMap{}|])
functionKMapWithOneItem =
    KMap
        testKMapDefinition
        [
            ( [trm| g{}() |]
            , [trm| \dv{SortTestKMapItem{}}("value") |]
            )
        ]
        Nothing

--------------------------------------------------------------------------------

testKListDef :: KListDefinition
testKListDef =
    KListDefinition
        { symbolNames =
            KCollectionSymbolNames
                { unitSymbolName = "Lbl'Stop'TestList"
                , elementSymbolName = "LblTestListItem"
                , concatSymbolName = "Lbl'Unds'TestList'Unds'"
                }
        , elementSortName = "SortTestListItem"
        , listSortName = "SortTestList"
        }

listConcatSym, listElemSym, listUnitSym :: Symbol
(listConcatSym, listElemSym, listUnitSym) = (withMeta cSym, withMeta eSym, withMeta uSym)
  where
    withMeta sym =
        sym
            { attributes = sym.attributes{collectionMetadata = Just $ KListMeta testKListDef}
            , sortVars = sym.sortVars
            }
    -- disambiguates the record update

    cSym =
        [symb| symbol Lbl'Unds'TestList'Unds'{}(SortTestList{}, SortTestList{}) : SortTestList{} [function{}(), total{}(), assoc{}()] |]
    eSym = [symb| symbol LblTestListItem{}(SomeSort{}) : SortTestList{} [function{}(), total{}()] |]
    uSym = [symb| symbol Lbl'Stop'TestList{}() : SortTestList{} [function{}(), total{}()] |]

listSymbols :: Map.Map ByteString Symbol
listSymbols =
    Map.fromList
        [ (testKListDef.symbolNames.unitSymbolName, listUnitSym)
        , (testKListDef.symbolNames.elementSymbolName, listElemSym)
        , (testKListDef.symbolNames.concatSymbolName, listConcatSym)
        ]

------------------------------------------------------------------------------

testKSetDef :: KSetDefinition
testKSetDef =
    KListDefinition
        { symbolNames =
            KCollectionSymbolNames
                { unitSymbolName = "Lbl'Stop'TestSet"
                , elementSymbolName = "LblTestSetItem"
                , concatSymbolName = "Lbl'Unds'TestSet'Unds'"
                }
        , elementSortName = "SortTestSetItem"
        , listSortName = "SortTestSet"
        }

setConcatSym, setElemSym, setUnitSym :: Symbol
(setConcatSym, setElemSym, setUnitSym) = (withMeta cSym, withMeta eSym, withMeta uSym)
  where
    withMeta sym =
        sym
            { attributes = sym.attributes{collectionMetadata = Just $ KSetMeta testKSetDef}
            , sortVars = sym.sortVars
            }
    -- disambiguates the record update

    cSym =
        [symb| symbol Lbl'Unds'TestSet'Unds'{}(SortTestSet{}, SortTestSet{}) : SortTestSet{} [function{}(), assoc{}()] |]
    eSym = [symb| symbol LblTestSetItem{}(SomeSort{}) : SortTestSet{} [function{}(), total{}()] |]
    uSym = [symb| symbol Lbl'Stop'TestSet{}() : SortTestSet{} [function{}(), total{}()] |]

setSymbols :: Map.Map ByteString Symbol
setSymbols =
    Map.fromList
        [ (testKSetDef.symbolNames.unitSymbolName, setUnitSym)
        , (testKSetDef.symbolNames.elementSymbolName, setElemSym)
        , (testKSetDef.symbolNames.concatSymbolName, setConcatSym)
        ]
