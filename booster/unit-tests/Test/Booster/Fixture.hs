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
                , kItemSort `withSubsorts` [someSort, aSubsort, differentSort]
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
        }
  where
    super `withSubsorts` subs =
        (getName super, (SortAttributes{argCount = 0}, Set.fromList (getName super : map getName subs)))
    -- sort variables and sort applications with arguments cause an error
    getName (SortApp n []) = n
    getName other = error $ "subSortOf: " <> show other <> " not supported"

var :: VarName -> Sort -> Term
var variableName variableSort = Var $ Variable{variableSort, variableName}

dv :: Sort -> ByteString -> Term
dv = DomainValue

app :: Symbol -> [Term] -> Term
app s = SymbolApplication s []

asTotalFunction, asPartialFunction, asConstructor :: SymbolAttributes
asTotalFunction = SymbolAttributes TotalFunction False False
asPartialFunction = SymbolAttributes PartialFunction False False
asConstructor = SymbolAttributes Constructor False False

con1, con2, con3, con4, f1, f2 :: Symbol
con1 =
    Symbol
        { name = "con1"
        , sortVars = []
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asConstructor
        }
con2 =
    Symbol
        { name = "con2"
        , sortVars = []
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asConstructor
        }
con3 =
    Symbol
        { name = "con3"
        , sortVars = []
        , resultSort = someSort
        , argSorts = [someSort, someSort]
        , attributes = asConstructor
        }
con4 =
    Symbol
        { name = "con4"
        , sortVars = []
        , resultSort = aSubsort
        , argSorts = [someSort, someSort]
        , attributes = asConstructor
        }
f1 =
    Symbol
        { name = "f1"
        , sortVars = []
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asTotalFunction
        }
f2 =
    Symbol
        { name = "f2"
        , sortVars = []
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asPartialFunction
        }
