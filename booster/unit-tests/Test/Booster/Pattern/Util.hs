module Test.Booster.Pattern.Util (
    test_subst,
    test_freshen,
) where

import Data.Map qualified as Map
import Data.Set qualified as Set
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

test_freshen :: TestTree
test_freshen =
    testGroup
        "Variable renaming"
        [ testGroup
            "Name-embedded variable counter increment"
            [ testCase "No counter gets 0 as counter" $ incrementNameCounter "Var'Ques'X" @?= "Var'Ques'X0"
            , testCase "0 counter gets incremented" $ incrementNameCounter "Var'Ques'X0" @?= "Var'Ques'X1"
            ]
        , testGroup
            "Variable name freshening by updating counter"
            [ testCase "No renaming when there's nothing to rename" $
                freshenVar (Variable someSort "X") (Set.fromList []) @?= Variable someSort "X"
            , testCase "One variable gets renamed" $
                freshenVar (Variable someSort "X1") (Set.fromList [Variable someSort "X1"])
                    @?= Variable someSort "X2"
            ]
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
asConstructor =
    SymbolAttributes
        Constructor
        IsNotIdem
        IsNotAssoc
        IsNotMacroOrAlias
        CanBeEvaluated
        Nothing
        Nothing
        Nothing

con1 :: Symbol
con1 =
    Symbol
        { name = "con1"
        , sortVars = []
        , resultSort = someSort
        , argSorts = [someSort]
        , attributes = asConstructor
        }
