{-# LANGUAGE QuasiQuotes #-}

{-# OPTIONS -Wno-incomplete-uni-patterns #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Pattern.Unify (
    test_unification,
) where

import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Pattern.Base
import Booster.Pattern.Unify
import Booster.Syntax.Json.Internalise (trm)
import Test.Booster.Fixture
import Test.Booster.Pattern.InternalCollections

test_unification :: TestTree
test_unification =
    testGroup
        "Unification"
        [ constructors
        , functions
        , varsAndValues
        , andTerms
        , sorts
        , injections
        , internalLists
        , internalMaps
        ]

injections :: TestTree
injections =
    testGroup
        "sort injections"
        [ test
            "same sort injection"
            (Injection aSubsort someSort varSub)
            (Injection aSubsort someSort dSub)
            $ success [("X", aSubsort, dSub)]
        , test
            "subsort injection"
            (Injection someSort kItemSort varSome)
            (Injection aSubsort kItemSort dSub)
            $ success [("Y", someSort, Injection aSubsort someSort dSub)]
        , let t1 = Injection someSort kItemSort varSome
              t2 = Injection differentSort kItemSort dOther
           in test "sort injection source mismatch" t1 t2 $ failed (DifferentSorts varSome dOther)
        , let t1 = Injection aSubsort someSort varSub
              t2 = Injection aSubsort kItemSort dOther
           in test "sort injection target mismatch" t1 t2 $ failed (DifferentSorts t1 t2)
        ]
  where
    varSub = var "X" aSubsort
    varSome = var "Y" someSort
    dSub = dv aSubsort "a subsort"
    dOther = dv differentSort "different sort"

sorts :: TestTree
sorts =
    testGroup
        "sort variables"
        [ test "sort variable in pattern" (app con1 [varX]) (app con1 [dSome]) $
            sortErr (FoundSortVariable "sort me!")
        , test "sort variable in subject" (app con1 [dSub]) (app con1 [varZ]) $
            sortErr (FoundSortVariable "me, too!")
        , test "several sort variables" (app con3 [varX, varY]) (app con3 [dSome, varZ]) $
            sortErr (FoundSortVariable "sort me!")
        ]
  where
    sVar = SortVar "sort me!"
    sVar2 = SortVar "me, too!"
    varX = var "X" sVar
    varY = var "Y" sVar
    varZ = var "Z" sVar2
    dSome = dv someSort "some sort"
    dSub = dv aSubsort "a subsort"

constructors :: TestTree
constructors =
    testGroup
        "Unifying constructors"
        [ test
            "same constructors, one variable argument"
            (app con1 [var "X" someSort])
            (app con1 [var "Y" someSort])
            (success [("X", someSort, var "Y" someSort)])
        , let x = var "X" someSort
              cX = app con1 [x]
           in test "same constructors, same variable (shared var)" cX cX $
                remainder [(x, x)]
        , let x = var "X" someSort
              y = var "Y" someSort
              cxx = app con3 [x, x]
              cxy = app con3 [x, y]
           in test "same constructors, one shared variable" cxx cxy $
                remainder [(x, x)]
        , let v = var "X" someSort
              d = dv differentSort ""
           in test
                "same constructors, arguments differ in sorts"
                (app con1 [v])
                (app con1 [d])
                (failed $ DifferentSorts v d)
        , test
            "same constructor, var./term argument"
            (app con1 [var "X" someSort])
            (app con1 [app f1 [var "Y" someSort]])
            (success [("X", someSort, app f1 [var "Y" someSort])])
        , let t1 = app con1 [var "X" someSort]
              t2 = app con2 [var "Y" someSort]
           in test "different constructors" t1 t2 $ failed (DifferentSymbols t1 t2)
        , let y = var "Y" someSort
              t1 = app con3 [var "X" someSort, var "X" someSort]
              t2 = app con3 [y, y]
           in test "Matching the same variable in a constructor (success)" t1 t2 $
                success [("X", someSort, y)]
        , let y = var "Y" someSort
              z = var "Z" someSort
              t1 = app con3 [var "X" someSort, var "X" someSort]
              t2 = app con3 [y, z]
           in test "Matching the same variable in a constructor (indeterminate)" t1 t2 $
                remainder [(y, z)]
        ]

functions :: TestTree
functions =
    testGroup
        "Functions (should not unify)"
        $ [ let f = app f1 [dv someSort ""]
             in test "exact same function (but not unifying)" f f $ remainder [(f, f)]
          , let f1T = app f1 [dv someSort ""]
                f2T = app f2 [dv someSort ""]
             in test "different functions" f1T f2T $ remainder [(f1T, f2T)]
          , let someDv = dv someSort ""
                f1T = app f1 [someDv]
                f2T = app f2 [someDv]
                con3f1 = app con3 [f1T, app con1 [someDv]]
                con3f2 = app con3 [f2T, app con1 [someDv]]
             in test "postponed: different functions" con3f1 con3f2 $ remainder [(f1T, f2T)]
          , let someDv = dv someSort ""
                f1T = app f1 [someDv]
                f2T = app f2 [someDv]
                c1T = app con1 [someDv]
                c2T = app con2 [someDv]
                con3f1c1 = app con3 [f1T, c1T]
                con3f2c2 = app con3 [f2T, c2T]
             in test "different constrs after different functions" con3f1c1 con3f2c2 $
                    failed (DifferentSymbols c1T c2T)
          ]
            ++ let f1T = app f1 [dv someSort ""]
                   dv1 = dv someSort ""
                   inj1 = Injection aSubsort someSort $ dv aSubsort ""
                in [ test "function with domain value" f1T dv1 $ remainder [(f1T, dv1)]
                   , test "domain value with function" dv1 f1T $ remainder [(dv1, f1T)]
                   , test "function with injection" f1T inj1 $ remainder [(f1T, inj1)]
                   , test "injection with function" inj1 f1T $ remainder [(inj1, f1T)]
                   ]

varsAndValues :: TestTree
varsAndValues =
    testGroup
        "Variables and Domain Values"
        [ let v = var "X" someSort
           in test "identical variables" v v (remainder [(v, v)])
        , let v1 = var "X" someSort
              v2 = var "Y" someSort
           in test "two variables (same sort)" v1 v2 $
                success [("X", someSort, v2)]
        , let v1 = var "X" someSort
              v2 = var "Y" aSubsort
           in test "two variables (v2 subsort v1)" v1 v2 $
                success [("X", someSort, v2)]
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
        ]

andTerms :: TestTree
andTerms =
    testGroup
        "And-terms on either side"
        [ let d = dv someSort "a"
              fa = app f1 [d]
              fb = app f1 [dv someSort "b"]
           in test
                "And-term on the left, remainder returns both pairs"
                (AndTerm fa fb)
                d
                (remainder [(fb, d), (fa, d)])
        , let d = dv someSort "a"
              fa = app f1 [d]
              fb = app f1 [dv someSort "b"]
           in test
                "And-term on the right, remainder returns both pairs"
                d
                (AndTerm fa fb)
                (remainder [(d, fb), (d, fa)])
        , let da = dv someSort "a"
              db = dv someSort "b"
              ca = app con1 [da]
              cb = app con1 [db]
           in test
                "And-term on the left, one unifies one fails"
                (AndTerm ca cb)
                ca
                (failed $ DifferentValues db da)
        , let da = dv someSort "a"
              db = dv someSort "b"
              ca = app con1 [da]
              cb = app con1 [db]
           in test
                "And-term on the right, one unifies one fails"
                ca
                (AndTerm cb ca)
                (failed $ DifferentValues da db)
        ]

internalLists :: TestTree
internalLists =
    testGroup
        "Internal lists"
        [ test
            "Can unify an empty list with itself"
            emptyList
            emptyList
            (success [])
        , test
            "Can unify a concrete list with itself"
            concreteList
            concreteList
            (success [])
        , test
            "Empty and non-empty concrete list fail to unify"
            emptyList
            concreteList
            (failed $ DifferentValues emptyList concreteList)
        , let two = klist (replicate 2 headElem) Nothing
              three = klist (replicate 3 headElem) Nothing
           in test
                "Concrete lists of different length fail to unify"
                two
                three
                (failed $ DifferentValues two three)
        , test
            "Empty and non-empty list fail to unify (symbolic tail)"
            headList
            emptyList
            (failed $ DifferentValues headList emptyList)
        , test
            "Empty and non-empty list fail to unify (symbolic init)"
            tailList
            emptyList
            (failed $ DifferentValues tailList emptyList)
        , test
            "Unification failures may swap the argument lists"
            emptyList
            tailList
            (failed $ DifferentValues tailList emptyList)
        , test
            "Head list and tail list produce indeterminate unification"
            headList
            tailList
            (remainder [(headList, tailList)])
        , test
            "Tail list and head list produce indeterminate unification"
            tailList
            headList
            (remainder [(tailList, headList)])
        , let listWithHeads = klist (replicate 3 headElem) Nothing
           in test
                "Can extract a single head element of a concrete list"
                headList -- "head":TAIL
                listWithHeads
                (success [("TAIL", listSort, klist (replicate 2 headElem) Nothing)])
        , let singletonList = klist [headElem] Nothing
              matchHead =
                klist [[trm| HEAD:SomeSort{} |]] $ Just ([trm| TAIL:SortTestList{} |], [])
           in test
                "Can extract a single head element of a singleton list"
                matchHead
                singletonList
                ( success
                    [ ("HEAD", someSort, headElem)
                    , ("TAIL", listSort, klist [] Nothing)
                    ]
                )
        , let KList _ hds (Just (v, tls)) = mixedList -- incomplete pattern match here
              tailElement = last tls
              initVariable = [trm| INIT:SortTestList{} |]
              matchTail = klist [] (Just (initVariable, [tailElement]))
              expected = klist hds (Just (v, init tls))
           in test
                "Can extract a single tail element of a mixed list"
                matchTail
                mixedList
                (success [("INIT", listSort, expected)])
        , let singletonList = klist [lastElem] Nothing
              matchTail = klist [] $ Just ([trm| INIT:SortTestList{} |], [[trm| LAST:SomeSort{} |]])
           in test
                "Can extract the tail element of a singleton list"
                matchTail
                singletonList
                ( success
                    [ ("LAST", someSort, lastElem)
                    , ("INIT", listSort, klist [] Nothing)
                    ]
                )
        , let list1 =
                klist
                    (replicate 3 headElem)
                    (Just (var "LIST1" listSort, replicate 2 lastElem))
              list2 =
                klist
                    (replicate 3 headElem)
                    (Just (var "LIST2" listSort, replicate 3 lastElem))
           in test
                "Unifies two lists with symbolic middle (binding LIST1)"
                list1
                list2
                (success [("LIST1", listSort, klist [] (Just (var "LIST2" listSort, [lastElem])))])
        , let list1 =
                klist
                    (replicate 3 headElem)
                    (Just (var "LIST1" listSort, replicate 2 lastElem))
              list2 =
                klist
                    (replicate 3 headElem)
                    (Just (var "LIST2" listSort, replicate 3 lastElem))
           in test
                "Unifies two lists with symbolic middle (binding LIST1), reverse direction"
                list2
                list1
                (success [("LIST1", listSort, klist [] (Just (var "LIST2" listSort, [lastElem])))])
        ]
  where
    headElem = [trm| \dv{SomeSort{}}("head") |]
    lastElem = [trm| \dv{SomeSort{}}("last") |]

    klist = KList testKListDef

internalMaps :: TestTree
internalMaps =
    testGroup
        "Internal maps"
        [ test
            "Can unify an empty map with itself"
            emptyKMap
            emptyKMap
            (success [])
        , test
            "Can unify a concrete 2 element map with itself"
            concreteKMapWithTwoItems
            concreteKMapWithTwoItems
            (success [])
        , test
            "Can unify a concrete and symbolic map"
            concreteKMapWithOneItem
            symbolicKMapWithOneItem
            (success [("A", kmapElementSort, [trm| \dv{SortTestKMapItem{}}("value")|])])
        , test
            "Can unify a concrete and symbolic map with two elements"
            concreteKMapWithTwoItems
            symbolicKMapWithTwoItems
            ( success
                [ ("A", kmapElementSort, [trm| \dv{SortTestKMapItem{}}("value")|])
                , ("B", kmapElementSort, [trm| \dv{SortTestKMapItem{}}("value2")|])
                ]
            )
        , test
            "Can unify {\"key\" |-> \"value\", ...REST} with {A |-> \"value\"}"
            concreteKMapWithOneItemAndRest
            symbolicKMapWithOneItem
            ( success
                [("REST", kmapSort, emptyKMap), ("A", kmapElementSort, [trm| \dv{SortTestKMapItem{}}("value")|])]
            )
        , test
            "Can unify {\"key\" |-> \"value\", A |-> \"value2\"} with {\"key\" |-> \"value\", ...REST}"
            concreteAndSymbolicKMapWithTwoItems
            concreteKMapWithOneItemAndRest
            ( success
                [
                    ( "REST"
                    , kmapSort
                    , KMap
                        testKMapDefinition
                        [
                            ( [trm| A:SortTestKMapKey{} |]
                            , [trm| \dv{SortTestKMapItem{}}("value2") |]
                            )
                        ]
                        Nothing
                    )
                ]
            )
        , test
            "Can unify {\"f()\" |-> B} with {\"f()\" |-> \"value\", ...REST}"
            functionKMapWithOneItem
            functionKMapWithOneItemAndRest
            ( success
                [
                    ( "REST"
                    , kmapSort
                    , KMap
                        testKMapDefinition
                        []
                        Nothing
                    )
                ,
                    ( "B"
                    , SortApp "SortTestKMapItem" []
                    , [trm| \dv{SortTestKMapItem{}}("value") |]
                    )
                ]
            )
        , test
            "Empty and non-empty concrete map fail to unify"
            emptyKMap
            concreteKMapWithOneItem
            (failed $ KeyNotFound [trm| \dv{SortTestKMapKey{}}("key")|] emptyKMap)
        , test
            "Concrete maps of different length fail to unify"
            concreteKMapWithOneItem
            concreteKMapWithTwoItems
            (failed $ KeyNotFound [trm| \dv{SortTestKMapKey{}}("key2")|] concreteKMapWithOneItem)
        , test
            "Empty and symbolic non-empty map fail to unify"
            emptyKMap
            symbolicKMapWithOneItem
            (failed $ KeyNotFound [trm| \dv{SortTestKMapKey{}}("key")|] emptyKMap)
        ]

----------------------------------------

success :: [(VarName, Sort, Term)] -> UnificationResult
success assocs =
    UnificationSuccess $
        Map.fromList
            [ (Variable{variableSort, variableName}, term)
            | (variableName, variableSort, term) <- assocs
            ]

failed :: FailReason -> UnificationResult
failed = UnificationFailed

remainder :: [(Term, Term)] -> UnificationResult
remainder = UnificationRemainder . NE.fromList

sortErr :: SortError -> UnificationResult
sortErr = UnificationSortError

test :: String -> Term -> Term -> UnificationResult -> TestTree
test name term1 term2 expected =
    testCase name $ unifyTerms testDefinition term1 term2 @?= expected
