{-# LANGUAGE QuasiQuotes #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Pattern.MatchEval (
    test_match_eval,
) where

import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Pattern.Base
import Booster.Pattern.Match
import Booster.Syntax.Json.Internalise (trm)
import Test.Booster.Fixture
import Test.Booster.Pattern.InternalCollections

test_match_eval :: TestTree
test_match_eval =
    testGroup
        "Equation/simplification matching"
        [ symbols
        , varsAndValues
        , cornerCases
        , andTerms
        , composite
        , kmapTerms
        , internalSets
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
              subj = app con2 [var "Y" someSort]
           in test "different constructors" pat subj $
                failed (DifferentSymbols pat subj)
        , let pat = app con1 [var "X" someSort]
              subj = app f1 [var "Y" someSort]
           in test "constructor and function" pat subj $
                MatchIndeterminate $
                    NE.singleton (pat, subj)
        , let pat = app f1 [var "X" someSort]
              subj = app con1 [var "Y" someSort]
           in test "function and constructor" pat subj $
                MatchIndeterminate $
                    NE.singleton (pat, subj)
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
                failed (VariableConflict (Variable someSort "X") v1 v2)
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
        , let v = var "X" someSort
              d = dv someSort ""
           in -- see https://github.com/runtimeverification/hs-backend-booster/issues/231
              test "dv matching a var (on RHS): indeterminate" d v $
                MatchIndeterminate $
                    NE.singleton (d, v)
        , let d = dv someSort ""
              f = app f1 [d]
           in test "dv matching a function call (on RHS): indeterminate" d f $
                MatchIndeterminate $
                    NE.singleton (d, f)
        , let d = dv someSort ""
              c = app con1 [d]
           in test "dv matching a constructor (on RHS): fail" d c $
                failed (DifferentSymbols d c)
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
                "And-term on the left, one matches one fails"
                (AndTerm ca cb)
                ca
                (failed $ DifferentValues db da)
        , let d = dv someSort "a"
              fa = app f1 [d]
              fb = app f1 [dv someSort "b"]
           in test
                "And-term on the right, indeterminate"
                d
                (AndTerm fa fb)
                (MatchIndeterminate $ NE.singleton (d, AndTerm fa fb))
        ]

kmapTerms :: TestTree
kmapTerms =
    testGroup
        "KMap on either side"
        [ test
            "Two empty KMaps: success with empty substitution"
            emptyKMap
            emptyKMap
            (success [])
        , test
            "Two identical concrete KMaps: success with empty substitution"
            concreteKMapWithOneItem
            concreteKMapWithOneItem
            (success [])
        , test
            "Non-empty concrete KMap ~= empty KMap: fails"
            concreteKMapWithOneItem
            emptyKMap
            (failed $ KeyNotFound [trm| \dv{SortTestKMapKey{}}("key")|] emptyKMap)
        , test
            "Non-empty symbolic KMap ~= empty KMap: fails"
            symbolicKMapWithOneItem
            emptyKMap
            (failed $ KeyNotFound [trm| \dv{SortTestKMapKey{}}("key")|] emptyKMap)
        , test
            "Non-empty symbolic KMap ~= non-empty concrete KMap, same key: matches contained value"
            symbolicKMapWithOneItem -- "key" -> A
            concreteKMapWithOneItem -- "key" -> "value"
            (success [("B", kmapElementSort, dv kmapElementSort "value")])
        , test
            "One key and rest variable ~= same key: Match rest with empty map"
            concreteKMapWithOneItemAndRest
            concreteKMapWithOneItem
            (success [("REST", kmapSort, emptyKMap)])
        , test
            "One key and rest variable ~= two keys (one the same): Match rest with other key singleton"
            concreteKMapWithOneItemAndRest
            concreteKMapWithTwoItems
            ( let restMap = kmap [(dv kmapKeySort "key2", dv kmapElementSort "value2")] Nothing
               in success [("REST", kmapSort, restMap)]
            )
        , -- pattern has more assocs than subject
          test
            "Extra concrete key in pattern, no rest in subject: fail on rest"
            concreteKMapWithTwoItems
            concreteKMapWithOneItem
            (failed $ KeyNotFound [trm| \dv{SortTestKMapKey{}}("key2")|] emptyKMap)
        , -- cases with disjoint keys
          test
            "Variable key ~= concrete key (and common element) without rest: match key"
            concreteAndSymbolicKMapWithTwoItems
            concreteKMapWithTwoItems
            ( success [("A", kmapKeySort, dv kmapKeySort "key2")]
            )
        , let patMap =
                kmap [([trm| K:SortTestKMapKey{} |], var "V" kmapElementSort)] (Just "PATTERN")
           in test
                "Variable key ~= concrete key with rest in subject and pattern: indeterminate"
                patMap
                functionKMapWithOneItemAndRest
                (MatchIndeterminate $ NE.singleton (patMap, functionKMapWithOneItemAndRest))
        , let patMap =
                kmap [(var "K" kmapKeySort, var "V" kmapElementSort)] (Just "PATTERN")
           in test
                "Variable key and opaque rest ~= two items: indeterminate"
                patMap
                concreteKMapWithTwoItems
                (MatchIndeterminate $ NE.singleton (patMap, concreteKMapWithTwoItems))
        , test
            "Pattern keys are fully-concrete, subject key function: indeterminate"
            concreteKMapWithOneItemAndRest
            functionKMapWithOneItem
            (MatchIndeterminate $ NE.singleton (concreteKMapWithOneItemAndRest, functionKMapWithOneItem))
        , let patMap =
                kmap
                    [ (var "A" kmapKeySort, dv kmapElementSort "a")
                    , (var "B" kmapKeySort, dv kmapElementSort "b")
                    ]
                    (Just "PATTERN")
              subjMap =
                kmap
                    [ (dv kmapKeySort "k1", dv kmapElementSort "a")
                    , (dv kmapKeySort "k2", dv kmapElementSort "b")
                    ]
                    (Just "SUBJECT")
           in test
                "Disjoint non-singleton maps, non-concrete keys in pattern: indeterminate"
                patMap
                subjMap
                (MatchIndeterminate $ NE.singleton (patMap, subjMap))
        ]
  where
    kmap :: [(Term, Term)] -> Maybe VarName -> Term
    kmap assocs mbRestVar =
        KMap testKMapDefinition assocs $ fmap (`var` kmapSort) mbRestVar

cornerCases :: TestTree
cornerCases =
    let v = var "X" someSort
     in errors "identical variables" v v

internalSets :: TestTree
internalSets =
    testGroup
        "Internal sets"
        [ test
            "Can match an empty set with itself"
            emptySet
            emptySet
            (success [])
        ]

----------------------------------------

test :: String -> Term -> Term -> MatchResult -> TestTree
test name pat subj expected =
    testCase name $ matchTerms Eval testDefinition pat subj @?= expected

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
        case matchTerms Eval testDefinition pat subj of
            MatchFailed _ -> pure ()
            other -> assertFailure $ "Expected MatchFailed, got " <> show other
