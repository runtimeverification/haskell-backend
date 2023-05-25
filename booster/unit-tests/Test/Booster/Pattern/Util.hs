module Test.Booster.Pattern.Util (
    test_subst,
) where

import Data.Map qualified as Map
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Definition.Attributes.Base
import Booster.Pattern.Base
import Booster.Pattern.Util

test_subst :: TestTree
test_subst =
    testGroup
        "Substitution"
        [ test
            "con1(X)[con1(Y)/X]"
            (Map.fromList [(Variable someSort "X", app con1 [var "Y" someSort])])
            (app con1 [var "X" someSort])
            (app con1 [app con1 [var "Y" someSort]])
        , test
            "con1(X)/\\con1(X)[con1(Y)/X]"
            (Map.fromList [(Variable someSort "X", app con1 [var "Y" someSort])])
            (AndTerm (app con1 [var "X" someSort]) (app con1 [var "X" someSort]))
            (AndTerm (app con1 [app con1 [var "Y" someSort]]) (app con1 [app con1 [var "Y" someSort]]))
        , test
            "con1(X)/\\con1(Y)[con1(Y)/X]"
            (Map.fromList [(Variable someSort "X", app con1 [var "Y" someSort])])
            (AndTerm (app con1 [var "X" someSort]) (app con1 [var "Y" someSort]))
            (AndTerm (app con1 [app con1 [var "Y" someSort]]) (app con1 [var "Y" someSort]))
        ]

----------------------------------------
-- Test fixture
test :: String -> Map.Map Variable Term -> Term -> Term -> TestTree
test name substitutions term expected =
    testCase name $ substituteInTerm substitutions term @?= expected

someSort :: Sort
someSort = SortApp "SomeSort" []

var :: VarName -> Sort -> Term
var variableName variableSort = Var $ Variable{variableSort, variableName}

app :: Symbol -> [Term] -> Term
app s = SymbolApplication s []

asConstructor :: SymbolAttributes
asConstructor = SymbolAttributes Constructor IsNotIdem IsNotAssoc IsNotMacroOrAlias Nothing

con1 :: Symbol
con1 =
    Symbol
        { name = "con1"
        , sortVars = []
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asConstructor
        }
