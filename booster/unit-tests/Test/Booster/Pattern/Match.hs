{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Pattern.Match (
    test_match,
) where

import Data.Map qualified as Map
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Pattern.Base
import Booster.Pattern.Match
import Booster.Pattern.Unify (FailReason (..))
import Test.Booster.Fixture

test_match :: TestTree
test_match =
    testGroup
        "(equation) matching"
        [ symbols
        , varsAndValues
        , cornerCases
        , andTerms
        , composite
        ]

symbols :: TestTree
symbols =
    testGroup
        "symbol applications (functions and constructors)"
        [ test
            "same constructor, variable argument"
            (app con1 [var "X" someSort])
            (app con1 [var "Y" someSort])
            (success [("X", someSort, var "Y" someSort)])
        , test
            "same function, argument matches"
            (app f1 [var "X" someSort])
            (app f1 [dv someSort "something"])
            (success [("X", someSort, dv someSort "something")])
        , let pat = app con1 [var "X" someSort]
              subj = app f1 [var "Y" someSort]
           in test "different constructors" pat subj $
                failed (DifferentSymbols pat subj)
        , let x = var "X" someSort
              d = dv differentSort "something"
              pat = app con1 [x]
              subj = app con1 [d]
           in test "same constructor, different argument sorts" pat subj $
                failed (DifferentSorts x d)
        , let pat = app f1 [var "X" someSort]
              subj = dv someSort "something"
           in test "function and something else" pat subj $
                failed (DifferentSymbols pat subj)
        ]

composite :: TestTree
composite =
    testGroup
        "composite (nested) symbols"
        [ let a = var "A" someSort
              b = var "B" someSort
              pat = app con3 [var "X" someSort, var "Y" someSort]
              subj = app con3 [a, b]
           in test "Matching two variables with variables" pat subj $
                success [("X", someSort, a), ("Y", someSort, b)]
        , let a = var "A" someSort
              b = var "B" someSort
              pat = app con3 [var "X" someSort, var "Y" someSort]
              subj = app con3 [app f1 [a], app f2 [b]]
           in test "Matching two variables with function applications" pat subj $
                success [("X", someSort, app f1 [a]), ("Y", someSort, app f2 [b])]
        , let a = var "A" someSort
              pat = app con3 [var "X" someSort, var "X" someSort] -- same!
              subj = app con3 [app f1 [a], app f1 [a]]
           in test "Matching two constructor argument to be the same (success)" pat subj $
                success [("X", someSort, app f1 [a])]
        , let a = var "A" someSort
              b = var "B" someSort
              pat = app con3 [var "X" someSort, var "X" someSort] -- same!
              subj = app con3 [a, b]
           in test "Matching two constructor argument to be the same (failing)" pat subj $
                failed (VariableConflict (Variable someSort "X") a b)
        ]

varsAndValues :: TestTree
varsAndValues =
    testGroup
        "Variables and values"
        [ let v1 = var "X" someSort
              v2 = var "Y" someSort
           in test "two variables (same sort)" v1 v2 $
                success [("X", someSort, v2)]
        , let v1 = var "X" someSort
              v2 = var "Y" aSubsort
           in test "two variables (v2 subsort v1)" v1 v2 $
                success [("X", someSort, inj aSubsort someSort v2)]
        , let v1 = var "X" aSubsort
              v2 = var "Y" someSort
           in test "two variables (v1 subsort v2)" v1 v2 $
                failed (DifferentSorts v1 v2)
        , let v1 = var "X" someSort
              v2 = var "X" differentSort
           in test "same variable name, different sort" v1 v2 $
                failed (DifferentSorts v1 v2)
        , let d1 = dv someSort "1"
              d2 = dv someSort "1"
           in test "same domain values (same sort)" d1 d2 $
                success []
        , let d1 = dv someSort "1"
              d2 = dv someSort "2"
           in test "different domain values (same sort)" d1 d2 $
                failed (DifferentValues d1 d2)
        , let d1 = dv someSort "1"
              d2 = dv differentSort "2"
           in test "different domain values (different sort)" d1 d2 $
                failed (DifferentValues d1 d2)
        , let d1 = dv someSort "1"
              d2 = dv differentSort "1"
           in test "same domain values, different sort" d1 d2 $
                failed (DifferentSorts d1 d2)
        , let v = var "X" someSort
              d = dv someSort ""
           in test "var and domain value (same sort)" v d $
                success [("X", someSort, d)]
        , let v = var "X" someSort
              d = dv differentSort ""
           in test "var and domain value (different sort)" v d $
                failed (DifferentSorts v d)
        ]

andTerms :: TestTree
andTerms =
    testGroup
        "And-terms on either side"
        [ let v = var "X" someSort
              f = app f1 [var "Y" someSort]
              d = dv someSort "something"
              subj = app f1 [d]
           in test
                "And-term on the left, match returns two bindings"
                (AndTerm v f)
                subj
                (success [("X", someSort, subj), ("Y", someSort, d)])
        , let da = dv someSort "a"
              db = dv someSort "b"
              ca = app con1 [da]
              cb = app con1 [db]
           in test
                "And-term on the left, one unifies one fails"
                (AndTerm ca cb)
                ca
                (failed $ DifferentValues db da)
        , let d = dv someSort "a"
              fa = app f1 [d]
              fb = app f1 [dv someSort "b"]
           in test
                "And-term on the right, fails"
                d
                (AndTerm fa fb)
                (failed $ DifferentValues d (AndTerm fa fb))
        ]

cornerCases :: TestTree
cornerCases =
    let v = var "X" someSort
     in errors "identical variables" v v

----------------------------------------

test :: String -> Term -> Term -> MatchResult -> TestTree
test name pat subj expected =
    testCase name $ matchTerm testDefinition pat subj @?= expected

success :: [(VarName, Sort, Term)] -> MatchResult
success assocs =
    MatchSuccess $
        Map.fromList
            [ (Variable{variableSort, variableName}, term)
            | (variableName, variableSort, term) <- assocs
            ]

failed :: FailReason -> MatchResult
failed = MatchFailed

errors :: String -> Term -> Term -> TestTree
errors name pat subj =
    testCase name $
        case matchTerm testDefinition pat subj of
            MatchError _ -> pure ()
            other -> assertFailure $ "Expected MatchError, got " <> show other
