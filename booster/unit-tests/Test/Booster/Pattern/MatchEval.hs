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
        , variableRebindMixedDeterminacy
        , functionApplicationAgainstConcreteCategories
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
                MatchIndeterminate mempty $
                    NE.singleton (pat, subj)
        , let pat = app f1 [var "X" someSort]
              subj = app con1 [var "Y" someSort]
           in test "function and constructor" pat subj $
                MatchIndeterminate mempty $
                    NE.singleton (pat, subj)
        , let x = var "X" someSort
              d = dv differentSort "something"
              pat = app con1 [x]
              subj = app con1 [d]
           in test "same constructor, different argument sorts" pat subj $
                failed (DifferentSorts x d)
        , let pat = app f1 [var "X" someSort]
              subj = dv someSort "something"
           in test "function and something else (indeterminate)" pat subj $
                remainder [(pat, subj)]
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
           in test "Matching two constructor argument to be the same (indeterminate)" pat subj $
                remainderWith [("X", someSort, a)] [(a, b)]
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
                MatchIndeterminate mempty $
                    NE.singleton (d, v)
        , let d = dv someSort ""
              f = app f1 [d]
           in test "dv matching a function call (on RHS): indeterminate" d f $
                MatchIndeterminate mempty $
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
                (MatchIndeterminate mempty $ NE.singleton (d, AndTerm fa fb))
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
                (MatchIndeterminate mempty $ NE.singleton (patMap, functionKMapWithOneItemAndRest))
        , let patMap =
                kmap [(var "K" kmapKeySort, var "V" kmapElementSort)] (Just "PATTERN")
           in test
                "Variable key and opaque rest ~= two items: indeterminate"
                patMap
                concreteKMapWithTwoItems
                (MatchIndeterminate mempty $ NE.singleton (patMap, concreteKMapWithTwoItems))
        , test
            "Pattern keys are fully-concrete, subject key function: indeterminate"
            concreteKMapWithOneItemAndRest
            functionKMapWithOneItem
            (MatchIndeterminate mempty $ NE.singleton (concreteKMapWithOneItemAndRest, functionKMapWithOneItem))
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
                (MatchIndeterminate mempty $ NE.singleton (patMap, subjMap))
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

{- | When a pattern variable is bound first to one term and then to
another where the two terms are not both constructor-like (e.g. a
domain value and a function application), the verdict must be
'MatchIndeterminate', because the function application could simplify
into the constructor-like term.

A decisive 'MatchFailed VariableConflict' here would be a soundness gap
for function-equation priorities: 'handleFunctionEquation'
(Pattern.ApplyEquations) routes @FailedMatch _@ to @continue@ but
@IndeterminateMatch{}@ to @abort@, so a spurious failure silently skips
a higher-priority equation and commits to a lower-priority one. The
tests below pin both orderings of the rebind.

The companion soundness regression test lives in
"Test.Booster.Pattern.ApplyEquations.test_soundnessGap".
-}
variableRebindMixedDeterminacy :: TestTree
variableRebindMixedDeterminacy =
    testGroup
        "Variable rebinding with mixed-determinacy subject"
        [ let d = dv someSort "1"
              fnApp = app f1 [dv someSort "x"]
              t1 = app con3 [var "X" someSort, var "X" someSort]
              t2 = app con3 [d, fnApp]
           in test
                "Rebind X to a domain value then to a function application is indeterminate"
                t1
                t2
                (remainderWith [("X", someSort, d)] [(d, fnApp)])
        , let d = dv someSort "1"
              fnApp = app f1 [dv someSort "x"]
              t1 = app con3 [var "X" someSort, var "X" someSort]
              t2 = app con3 [fnApp, d]
           in test
                "Rebind X to a function application then to a domain value is indeterminate"
                t1
                t2
                (remainderWith [("X", someSort, fnApp)] [(fnApp, d)])
        ]

{- | When the pattern (rule LHS) contains a function application and the
subject in that position is a structured term — an injection, a map, a
list, or a set — the verdict must be 'MatchIndeterminate', because the
function application could in principle simplify into the corresponding
category. A decisive 'MatchFailed DifferentSymbols' (as 'Eval' mode
returned before this was fixed) would unsoundly skip a higher-priority
function equation. The four tests pin the @FunctionApplication{}@
pattern paired with @Injection{} / KMap{} / KList{} / KSet{}@ subjects;
the companion case for @DomainValue{}@ is covered by an existing test
in the 'symbols' group.
-}
functionApplicationAgainstConcreteCategories :: TestTree
functionApplicationAgainstConcreteCategories =
    testGroup
        "FunctionApplication pattern against concrete categories"
        [ let pat = app f1 [var "X" someSort]
              subj = Injection aSubsort someSort (dv aSubsort "x")
           in test
                "FunctionApplication pattern with Injection subject is indeterminate"
                pat
                subj
                (remainder [(pat, subj)])
        , let pat = app f1 [var "X" someSort]
              subj = emptyKMap
           in test
                "FunctionApplication pattern with KMap subject is indeterminate"
                pat
                subj
                (remainder [(pat, subj)])
        , let pat = app f1 [var "X" someSort]
              subj = emptyList
           in test
                "FunctionApplication pattern with KList subject is indeterminate"
                pat
                subj
                (remainder [(pat, subj)])
        , let pat = app f1 [var "X" someSort]
              subj = emptySet
           in test
                "FunctionApplication pattern with KSet subject is indeterminate"
                pat
                subj
                (remainder [(pat, subj)])
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

remainder :: [(Term, Term)] -> MatchResult
remainder = MatchIndeterminate mempty . NE.fromList

{- | Like 'remainder' but also asserts a non-empty partial substitution
from pairs that the matcher resolved before reaching the indeterminate
pairs.
-}
remainderWith :: [(VarName, Sort, Term)] -> [(Term, Term)] -> MatchResult
remainderWith assocs pairs =
    MatchIndeterminate
        ( Map.fromList
            [ (Variable{variableSort, variableName}, term)
            | (variableName, variableSort, term) <- assocs
            ]
        )
        (NE.fromList pairs)

errors :: String -> Term -> Term -> TestTree
errors name pat subj =
    testCase name $
        case matchTerms Eval testDefinition pat subj of
            MatchFailed _ -> pure ()
            other -> assertFailure $ "Expected MatchFailed, got " <> show other
