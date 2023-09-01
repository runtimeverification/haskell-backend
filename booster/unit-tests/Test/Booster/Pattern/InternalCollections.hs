{-# LANGUAGE QuasiQuotes #-}

{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Test.Booster.Pattern.InternalCollections (
    test_collections,
    emptyList,
    concreteList,
    headList,
    tailList,
    mixedList,
) where

import Test.Tasty
import Test.Tasty.HUnit

import Booster.Pattern.Base
import Booster.Syntax.Json.Internalise (trm)
import Test.Booster.Fixture as Fixture

test_collections :: TestTree
test_collections =
    testGroup
        "Internal collection representation"
        [ listRoundTrips
        , internalising
        ]

-- round-tripping from internal through external and back
listRoundTrips :: TestTree
listRoundTrips =
    testGroup
        "List round-trip conversions"
        [ roundTrip "empty list" emptyList
        , roundTrip "concrete list" concreteList
        , roundTrip "head list" headList
        , roundTrip "tail list" tailList
        , roundTrip "mixed list" mixedList
        ]
  where
    roundTrip :: String -> Term -> TestTree
    roundTrip name listTerm@(KList def heads rest) =
        testCase name $ listTerm @=? internaliseKList def (externaliseKList def heads rest)
    roundTrip name otherTerm =
        testCase name $ assertFailure $ "contains a non-list term" <> show otherTerm

internalising :: TestTree
internalising =
    testGroup
        "Internalising lists"
        [ testCase "Empty list" $ internalise unit @=? emptyList
        , let headAndRest =
                listConcat (inList [trm| \dv{SomeSort{}}("head") |]) [trm| TAIL:SortTestList{} |]
           in testCase "Head list" $ internalise headAndRest @=? headList
        , let restAndTail =
                listConcat [trm| INIT:SortTestList{} |] (inList [trm| \dv{SomeSort{}}("last") |])
           in testCase "Tail list" $ internalise restAndTail @=? tailList
        , -- , let restAndTail =
          --           [trm| Lbl'Unds'TestList'Unds'{}(REST:SortTestList{}, \dv{SomeSort{}}("tail")) |]
          --    in testCase "Tail list 2" $ internalise restAndTail @=? tailList
          let thingleton = inList [trm| \dv{SomeSort{}}("thing") |]
              threeThings = listConcat (listConcat thingleton thingleton) thingleton
           in testCase "Three things" $ internalise threeThings @=? concreteList
        , let before =
                listConcat
                    (inList [trm| \dv{SomeSort{}}("variable follows") |])
                    [trm| REST:SortTestList{} |]
              listAfter =
                foldl1 listConcat $
                    replicate 4 $
                        inList [trm| \dv{SomeSort{}}("after variable") |]
           in testCase "mixing a list" $ internalise (listConcat before listAfter) @=? mixedList
        ]
  where
    internalise = internaliseKList Fixture.testKListDef
    unit = SymbolApplication unitSym [] []

-- internalised data structures representing variants of lists
emptyList, concreteList, headList, tailList, mixedList :: Term
emptyList =
    KList testKListDef [] Nothing
concreteList =
    KList testKListDef (replicate 3 [trm| \dv{SomeSort{}}("thing")|]) Nothing
headList =
    KList
        testKListDef
        [[trm| \dv{SomeSort{}}("head")|]]
        $ Just ([trm| TAIL:SortTestList{}|], [])
tailList =
    KList
        testKListDef
        []
        $ Just ([trm| INIT:SortTestList{}|], [[trm| \dv{SomeSort{}}("last")|]])
mixedList =
    KList
        testKListDef
        [[trm| \dv{SomeSort{}}("variable follows")|]]
        $ Just
            ( [trm| REST:SortTestList{}|]
            , replicate 4 [trm| \dv{SomeSort{}}("after variable")|]
            )

listConcat :: Term -> Term -> Term
listConcat l1 l2 = SymbolApplication concatSym [] [l1, l2]

inList :: Term -> Term
inList x = SymbolApplication elemSym [] [x]
