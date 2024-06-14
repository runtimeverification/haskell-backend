module Test.Booster.Pattern.PartialOrder (
    test_transitiveClosure,
) where

import Data.Set qualified as Set
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Pattern.Base
import Booster.Pattern.Bool
import Booster.Pattern.PartialOrder

test_transitiveClosure :: TestTree
test_transitiveClosure =
    testGroup
        "<Int --- strict partial order"
        [ test
            "No new items"
            ltIntSymbol
            ( [ LtInt (var "A") (var "B")
              , LtInt (var "C") (var "D")
              ]
            )
            ( []
            )
        , test
            "One new item"
            ltIntSymbol
            ( [ LtInt (var "A") (var "B")
              , LtInt (var "B") (var "C")
              ]
            )
            ( [ LtInt (var "A") (var "C")
              ]
            )
        , test
            "Two new items"
            ltIntSymbol
            ( [ LtInt (var "A") (var "B")
              , LtInt (var "B") (var "C")
              , LtInt (var "B") (var "D")
              ]
            )
            ( [ LtInt (var "A") (var "C")
              , LtInt (var "A") (var "D")
              ]
            )
        , test
            "Cycle, no new items"
            ltIntSymbol
            ( [ LtInt (var "A") (var "B")
              , LtInt (var "B") (var "A")
              ]
            )
            ( []
            )
        ]

----------------------------------------
-- Test fixture
test :: String -> Symbol -> [Term] -> [Term] -> TestTree
test name sym input expected =
    testCase name $
        transitiveClosure sym (Set.fromList $ map Predicate input)
            @?= (Set.fromList $ map Predicate expected)

ltIntSymbol :: Symbol
ltIntSymbol =
    case LtInt (var "DUMMY") (var "DUMMY") of
        SymbolApplication ltInt _ _ -> ltInt
        _ -> error "Impossible"

someSort :: Sort
someSort = SortApp "SomeSort" []

var :: VarName -> Term
var variableName = Var $ Variable{variableSort = someSort, variableName}
