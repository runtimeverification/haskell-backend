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
import Booster.Syntax.Json.Internalise (trm)
import Booster.Syntax.ParsedKore.Internalise (symb)

someSort, aSubsort, differentSort, kSort, kItemSort :: Sort
someSort = SortApp "SomeSort" []
aSubsort = SortApp "AnotherSort" []
differentSort = SortApp "DifferentSort" []
kSort = SortApp "SortK" []
kItemSort = SortApp "SortKItem" []

testDefinition :: KoreDefinition
testDefinition =
    KoreDefinition
        { attributes = DefinitionAttributes
        , modules = Map.singleton "AMODULE" ModuleAttributes
        , sorts =
            Map.fromList
                [ someSort `withSubsorts` [aSubsort]
                , aSubsort `withSubsorts` []
                , differentSort `withSubsorts` []
                , kSort `withSubsorts` []
                ]
        , symbols =
            Map.fromList
                [ ("con1", con1)
                , ("con2", con2)
                , ("con3", con3)
                , ("con4", con4)
                , ("f1", f1)
                , ("f2", f2)
                ]
        , aliases = Map.empty
        , rewriteTheory = Map.empty
        , functionEquations = Map.empty
        , simplifications = Map.empty
        , predicateSimplifications = Map.empty
        }
  where
    super `withSubsorts` subs =
        ( getName super
        ,
            ( SortAttributes{argCount = 0, kmapAttributes = Nothing}
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

con1, con2, con3, con4, f1, f2 :: Symbol
con1 = [symb| symbol con1{}(SomeSort{}) : SomeSort{} [constructor{}()] |]
con2 = [symb| symbol con2{}(SomeSort{}) : SomeSort{} [constructor{}()] |]
con3 = [symb| symbol con3{}(SomeSort{}, SomeSort{}) : SomeSort{} [constructor{}()] |]
con4 = [symb| symbol con4{}(SomeSort{}, SomeSort{}) : AnotherSort{} [constructor{}()] |]
f1 = [symb| symbol f1{}(SomeSort{}) : SomeSort{} [function{}(), total{}()] |]
f2 = [symb| symbol f2{}(SomeSort{}) : SomeSort{} [function{}()] |]

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
        KMapAttributes
            { unitSymbolName = "Lbl'Stop'TestKMap"
            , elementSymbolName = "LblTestKMapItem"
            , concatSymbolName = "Lbl'Unds'TestKMap'Unds'"
            }

emptyKMap, concreteKMapWithOneItem, symbolicKMapWithOneItem :: Term
emptyKMap = KMap testKMapDefinition [] Nothing
concreteKMapWithOneItem =
    KMap
        testKMapDefinition
        [
            ( [trm| \dv{SomeSort{}}("key")|]
            , [trm| \dv{SomeSort{}}("value")|]
            )
        ]
        Nothing
symbolicKMapWithOneItem =
    KMap
        testKMapDefinition
        [
            ( [trm| \dv{SomeSort{}}("key")|]
            , [trm| A:SomeSort|]
            )
        ]
        Nothing
