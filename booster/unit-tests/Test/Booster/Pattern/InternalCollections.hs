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

import Data.ByteString.Char8 qualified as BS
import Data.List qualified as List
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Pattern.Base
import Booster.Syntax.Json.Internalise (trm)
import Test.Booster.Fixture qualified as Fixture

test_collections :: TestTree
test_collections =
    testGroup
        "Internal collection representation"
        [ listRoundTrips
        , listInternalisation
        , setRoundTrips
        , setInternalisation
        ]

------------------------------------------------------------

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

listInternalisation :: TestTree
listInternalisation =
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
    unit = SymbolApplication Fixture.listUnitSym [] []

-- internalised data structures representing variants of lists
emptyList, concreteList, headList, tailList, mixedList :: Term
emptyList =
    KList Fixture.testKListDef [] Nothing
concreteList =
    KList Fixture.testKListDef (replicate 3 [trm| \dv{SomeSort{}}("thing")|]) Nothing
headList =
    KList
        Fixture.testKListDef
        [[trm| \dv{SomeSort{}}("head")|]]
        $ Just ([trm| TAIL:SortTestList{}|], [])
tailList =
    KList
        Fixture.testKListDef
        []
        $ Just ([trm| INIT:SortTestList{}|], [[trm| \dv{SomeSort{}}("last")|]])
mixedList =
    KList
        Fixture.testKListDef
        [[trm| \dv{SomeSort{}}("variable follows")|]]
        $ Just
            ( [trm| REST:SortTestList{}|]
            , replicate 4 [trm| \dv{SomeSort{}}("after variable")|]
            )

listConcat :: Term -> Term -> Term
listConcat l1 l2 = Term mempty $ SymbolApplicationF Fixture.listConcatSym [] [l1, l2]

inList :: Term -> Term
inList x = SymbolApplication Fixture.listElemSym [] [x]

------------------------------------------------------------

-- round-tripping from internal through external and back
setRoundTrips :: TestTree
setRoundTrips =
    testGroup
        "Set round-trip conversions"
        [ roundTrip "empty set" emptySet
        , roundTrip "concrete set" concreteSet
        , roundTrip "set pattern matching an element" setWithElement
        ]
  where
    roundTrip :: String -> Term -> TestTree
    roundTrip name setTerm@(KSet def heads rest) =
        testCase name $ setTerm @=? internaliseKSet def (externaliseKSet def heads rest)
    roundTrip name otherTerm =
        testCase name $ assertFailure $ "contains a non-set term" <> show otherTerm

setInternalisation :: TestTree
setInternalisation =
    testGroup
        "Internalising sets"
        [ testCase "Empty set" $ emptySet @=? internalise unit
        , let oneElemList =
                setConcat
                    (inSet [trm| \dv{SomeSort{}}("element")|])
                    [trm| REST:SortTestSet{} |]
           in testCase "Set with element" $
                setWithElement @=? internalise oneElemList
        , let fullyConcrete =
                foldr1 setConcat
                    $ map inSet
                        . List.sort
                    $ map (Fixture.dv Fixture.someSort . BS.pack . show @Int) [1 .. 3]
           in testCase "Fully concrete set" $
                concreteSet @=? internalise fullyConcrete
        , let var1, var2 :: Term
              var1 = Fixture.var "VAR1" Fixture.setSort
              var2 = Fixture.var "VAR2" Fixture.setSort
              e1 = [trm| \dv{SomeSort{}}("1") |]
              e2 = [trm| \dv{SomeSort{}}("2") |]
              e3 = [trm| \dv{SomeSort{}}("3") |]
              twoVarsSet =
                setConcat
                    (setConcat (inSet e1) $ setConcat (inSet e2) var1)
                    (setConcat (inSet e3) var2)
              result =
                KSet
                    Fixture.testKSetDef
                    (List.sort [e1, e2, e3])
                    (Just $ SymbolApplication Fixture.setConcatSym [] [var1, var2])
           in testCase "two variables and some concrete elements in set, concat pushed inwards" $
                result @=? internalise twoVarsSet
        ]
  where
    internalise = internaliseKSet Fixture.testKSetDef
    unit = SymbolApplication Fixture.setUnitSym [] []

-- internalised data structures representing sets
emptySet, concreteSet, setWithElement :: Term
emptySet =
    KSet Fixture.testKSetDef [] Nothing
concreteSet =
    KSet
        Fixture.testKSetDef
        ( List.sort
            [ [trm| \dv{SomeSort{}}("1")|]
            , [trm| \dv{SomeSort{}}("2")|]
            , [trm| \dv{SomeSort{}}("3")|]
            ]
        )
        Nothing
setWithElement =
    KSet
        Fixture.testKSetDef
        [[trm| \dv{SomeSort{}}("element") |]]
        (Just [trm| REST:SortTestSet{}|])

setConcat :: Term -> Term -> Term
setConcat l1 l2 = Term mempty $ SymbolApplicationF Fixture.setConcatSym [] [l1, l2]

inSet :: Term -> Term
inSet x = SymbolApplication Fixture.setElemSym [] [x]
