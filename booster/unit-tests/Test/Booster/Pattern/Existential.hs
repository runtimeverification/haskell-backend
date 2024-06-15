module Test.Booster.Pattern.Existential (
    test_matchExistential,
    test_instantiateExistentials,
) where

import Data.Map.Strict (Map)
import Data.Map.Strict qualified as Map
import Data.Set qualified as Set
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Pattern.Base
import Booster.Pattern.Bool
import Booster.Pattern.Existential

test_matchExistential :: TestTree
test_matchExistential =
    testGroup
        "matchExistential"
        [ testGroup
            "positive cases -- non-empty substitution"
            [ test
                "One existential -- one binding, left"
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "B"))
                (Predicate $ LtInt (varTerm "C") (varTerm "D"))
                ( Map.fromList [(var "Ex#A", varTerm "C")]
                )
            , test
                "One existential -- one binding, right"
                (Predicate $ LtInt (varTerm "A") (varTerm "Ex#B"))
                (Predicate $ LtInt (varTerm "C") (varTerm "D"))
                ( Map.fromList [(var "Ex#B", varTerm "D")]
                )
            , test
                "Two existentials -- two bindings"
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "Ex#B"))
                (Predicate $ LtInt (varTerm "C") (varTerm "D"))
                ( Map.fromList [(var "Ex#A", varTerm "C"), (var "Ex#B", varTerm "D")]
                )
            ]
        , testGroup
            "negative cases -- empty substitution"
            [ test
                "No existentials"
                (Predicate $ LtInt (varTerm "A") (varTerm "B"))
                (Predicate $ LtInt (varTerm "C") (varTerm "D"))
                (Map.empty)
            , test
                "Different symbols"
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "Ex#B"))
                (Predicate $ EqualsInt (varTerm "C") (varTerm "D"))
                (Map.empty)
            , test
                "Malformed target -- not a symbol application"
                (Predicate $ varTerm "A")
                (Predicate $ LtInt (varTerm "C") (varTerm "D"))
                (Map.empty)
            , test
                "Malformed known -- not a symbol application"
                (Predicate $ LtInt (varTerm "Ex#C") (varTerm "D"))
                (Predicate $ varTerm "A")
                (Map.empty)
            ]
        ]
  where
    test :: String -> Predicate -> Predicate -> Map Variable Term -> TestTree
    test name target known expected =
        testCase name $
            matchExistential target known
                @?= expected

test_instantiateExistentials :: TestTree
test_instantiateExistentials =
    testGroup
        "instantiateExistentials"
        [ testGroup
            "positive cases -- changed predicate"
            [ test
                "Earlier bindings are preferred"
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "Ex#B"))
                [ Predicate $ LtInt (varTerm "C1") (varTerm "D1")
                , Predicate $ LtInt (varTerm "C2") (varTerm "D2")
                ]
                (Predicate $ LtInt (varTerm "C1") (varTerm "D1"))
            , test
                "Can ignore non-matching known"
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "Ex#B"))
                [ Predicate $ EqualsInt (varTerm "C1") (varTerm "D1")
                , Predicate $ LtInt (varTerm "C2") (varTerm "D2")
                ]
                (Predicate $ LtInt (varTerm "C2") (varTerm "D2"))
            ]
        , testGroup
            "negative cases -- same predicate"
            [ test
                "No matching known"
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "Ex#B"))
                [ Predicate $ EqualsInt (varTerm "C1") (varTerm "D1")
                , Predicate $ EqualsInt (varTerm "C2") (varTerm "D2")
                ]
                (Predicate $ LtInt (varTerm "Ex#A") (varTerm "Ex#B"))
            , test
                "No existentials"
                (Predicate $ LtInt (varTerm "A") (varTerm "B"))
                [ Predicate $ EqualsInt (varTerm "C1") (varTerm "D1")
                , Predicate $ EqualsInt (varTerm "C2") (varTerm "D2")
                ]
                (Predicate $ LtInt (varTerm "A") (varTerm "B"))
            ]
        ]
  where
    test :: String -> Predicate -> [Predicate] -> Predicate -> TestTree
    test name target known expected =
        testCase name $
            instantiateExistentials (Set.fromList known) target
                @?= expected

----------------------------------------

someSort :: Sort
someSort = SortApp "SomeSort" []

var :: VarName -> Variable
var variableName = Variable{variableSort = someSort, variableName}

varTerm :: VarName -> Term
varTerm variableName = Var $ Variable{variableSort = someSort, variableName}
