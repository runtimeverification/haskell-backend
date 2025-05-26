{-# LANGUAGE QuasiQuotes #-}

{- |
Copyright   : (c) Runtime Verification, 2024
License     : BSD-3-Clause
-}
module Test.Booster.Builtin (
    test_builtins,
) where

import Control.Monad.Trans.Except
import Data.Bifunctor (second)
import Data.ByteString.Char8 qualified as BS
import Data.Either (isLeft)
import Data.Function (on)
import Data.List (nubBy)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Set qualified as Set
import Data.Text qualified as Text

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Hedgehog

import Booster.Builtin qualified as Builtin (hooks)
import Booster.Builtin.BOOL qualified as Builtin
import Booster.Builtin.Base qualified as Builtin (BuiltinFunction)
import Booster.Builtin.INT qualified as Builtin
import Booster.Builtin.LIST qualified as Builtin (kItemListDef)
import Booster.Pattern.Base
import Booster.Syntax.Json.Internalise (trm)
import Booster.Syntax.ParsedKore.Internalise (symb)
import Test.Booster.Fixture as Fixture

test_builtins :: [TestTree]
test_builtins =
    [ testIntHooks
    , testListHooks
    , testMapHooks
    ]

testIntHooks :: TestTree
testIntHooks =
    testGroup
        "Integer hooks"
        [ testIntHook2 "INT.add" (+) Builtin.intTerm
        , testIntHook2 "INT.mul" (*) Builtin.intTerm
        , testIntHook2 "INT.sub" (-) Builtin.intTerm
        , -- comparisons
          testIntHook2 "INT.gt" (>) Builtin.boolTerm
        , testIntHook2 "INT.ge" (>=) Builtin.boolTerm
        , testIntHook2 "INT.lt" (<) Builtin.boolTerm
        , testIntHook2 "INT.le" (<=) Builtin.boolTerm
        , testIntHook2 "INT.eq" (==) Builtin.boolTerm
        , testIntHook2 "INT.ne" (/=) Builtin.boolTerm
        ]
  where
    -- testIntHook2 :: ByteString -> (Int -> Int -> a) -> (a -> Term) -> TestTree
    testIntHook2 name op result =
        testProperty ("Hook " <> show name) . property $ do
            let f = runHook name
                run args = either (error . Text.unpack) id . runExcept $ f args
            a <- fmap fromIntegral $ forAll $ Gen.int64 Range.linearBounded
            b <- fmap fromIntegral $ forAll $ Gen.int64 Range.linearBounded
            let dv_a = Builtin.intTerm a
                dv_b = Builtin.intTerm b
            -- regular computation
            Just (result $ op a b) === run [dv_a, dv_b]
            -- Nothing for unevaluated arguments
            let fct = [symb| symbol f{}(SortInt) : SortInt [function{}()] |]
            Nothing === run [app fct [dv_a], dv_b]
            Nothing === run [dv_a, app fct [dv_b]]
            Nothing === run [app fct [dv_a], app fct [dv_b]]
            -- arity error on wrong argument count
            let assertException = assert . isLeft . runExcept
            assertException $ f []
            assertException $ f [dv_a]
            assertException $ f [dv_a, dv_a, dv_a]

testListHooks :: TestTree
testListHooks =
    testGroup
        "LIST hooks"
        [ testListArityChecks
        , testListConcatHook
        , testListElementHook
        , testListGetHook
        , testListInHook
        , testListMakeHook
        , testListRangeHook
        , testListSizeHook
        , testListUpdateHook
        ]

testListArityChecks :: TestTree
testListArityChecks =
    testGroup
        "Arity of list hooks is checked"
        [ testCase "LIST.concat: 2 list arg.s" $ do
            assertException "LIST.concat" []
            assertException "LIST.concat" [[trm| X:SortList |]]
            assertException "LIST.concat" $ replicate 3 [trm| X:SortList |]
        , --        , error "missing arity checks!"
          testCase "LIST.size: list arg." $ do
            assertException "LIST.size" []
            assertException "LIST.size" $ replicate 2 [trm| X:SortList |]
        , testCase "LIST.get: list and int arg.s" $ do
            assertException "LIST.get" []
            assertException "LIST.get" [[trm| X:SortList |]]
            assertException "LIST.get" $ replicate 3 [trm| X:SortList{} |]
        , testCase "LIST.update: list, index, and element" $ do
            assertException "LIST.update" []
            assertException "LIST.update" [[trm| X:SortList |]]
            assertException "LIST.update" $ replicate 2 [trm| X:SortList{} |]
            assertException "LIST.update" $ replicate 4 [trm| X:SortList{} |]
        ]
  where
    assertException name =
        assertBool "Unexpected success" . isLeft . runExcept . runHook name

-- list and element helpers
listOfThings :: Int -> Term
listOfThings n =
    let things = map numDV [1 .. n]
     in KList Fixture.testKListDef things Nothing

-- wrap an Int into an injection to KItem here
numDV :: Int -> Term
numDV n =
    Fixture.inj Fixture.someSort Fixture.kItemSort $ dv Fixture.someSort $ BS.pack $ show n

-- this assumes all terms are sort KItem or that sorts are irrelevant
kitemList :: [Term] -> Term
kitemList items = KList Builtin.kItemListDef items Nothing

testListConcatHook :: TestTree
testListConcatHook =
    testGroup
        "LIST.concat hook"
        [ testCase "LIST.concat on two empty lists" $ do
            let empty = listOfThings 0
            result <- evalHook "LIST.concat" [empty, empty]
            Just empty @=? result
        , testProperty "LIST.concat with an empty list argument" . property $ do
            l <- forAll smallNat
            let aList = listOfThings l
                empty = listOfThings 0
            resultR <- evalHook "LIST.concat" [aList, empty]
            Just aList === resultR
            resultL <- evalHook "LIST.concat" [empty, aList]
            Just aList === resultL
        , testProperty "LIST.concat with concrete lists" . property $ do
            l1 <- forAll smallNat
            l2 <- forAll smallNat
            let list1 = listOfThings l1
                list2 = listOfThings l2
                expected = map numDV $ [1 .. l1] <> [1 .. l2]
            result <- evalHook "LIST.concat" [list1, list2]
            Just (KList Fixture.testKListDef expected Nothing) === result
        , testProperty "LIST.concat with one opaque middle term" . property $ do
            l1 <- forAll smallNat
            l1t <- forAll smallNat
            l2 <- forAll smallNat
            let heads1 = map numDV [1 .. l1]
                tail1 = Just ([trm| M1:SortList |], map numDV [1 .. l1t])
                heads2 = map numDV [1 .. l2]
                list1 = KList Fixture.testKListDef heads1 tail1
                list2 = KList Fixture.testKListDef heads2 Nothing
            result <- evalHook "LIST.concat" [list1, list2]
            let expectedTail = Just ([trm| M1:SortList |], map numDV $ [1 .. l1t] <> [1 .. l2])
            Just (KList Fixture.testKListDef heads1 expectedTail) === result
            result2 <- evalHook "LIST.concat" [list2, list1]
            Just (KList Fixture.testKListDef (heads2 <> heads1) tail1) === result2
        , testProperty "LIST.concat with two opaque middle terms: indeterminate" . property $ do
            l1 <- forAll smallNat
            l1t <- forAll smallNat
            l2 <- forAll smallNat
            l2t <- forAll smallNat
            let list1 =
                    KList Fixture.testKListDef (map numDV [1 .. l1]) $
                        Just ([trm| M1:SortList |], map numDV [1 .. l1t])
            let list2 =
                    KList Fixture.testKListDef (map numDV [1 .. l2]) $
                        Just ([trm| M2:SortList |], map numDV [1 .. l2t])
            result <- evalHook "LIST.concat" [list1, list2]
            Nothing === result
        ]

testListElementHook :: TestTree
testListElementHook =
    testGroup
        "LIST.element"
        [ testCase "making a singleton list" $ do
            let thing = [trm| THING:SortKItem |]
            result <- evalHook "LIST.element" [thing]
            -- this will return the fixed built-in list metadata
            Just (kitemList [thing]) @=? result
        ]

testListInHook :: TestTree
testListInHook =
    testGroup
        "LIST.in"
        [ testCase "LIST.in is false when the list is empty" $ do
            let thing = numDV 0
                empty = listOfThings 0
            result <- evalHook "LIST.in" [thing, empty]
            result `_shouldBe_` False
        , testProperty "LIST.in is true when an item is present in the head" . property $ do
            l <- forAll $ between1And 42
            k <- forAll $ between1And l
            let list = listOfThings l -- [1 .. l]
                target = numDV k
            result <- evalHook "LIST.in" [target, list]
            result `shouldBe` True
        , testProperty "LIST.in is true when an item is present in the tail" . property $ do
            l <- forAll $ between1And 42
            k <- forAll $ between1And l
            let elems = map numDV [1 .. l]
                list = KList Fixture.testKListDef [] $ Just ([trm| INIT:SortList |], elems)
                target = numDV k
            result <- evalHook "LIST.in" [target, list]
            result `shouldBe` True
        , testProperty "LIST.in is false when an item is not present (concrete list)" . property $ do
            l <- forAll smallNat
            let list = listOfThings l -- [1 .. l]
                target = numDV 0
            result <- evalHook "LIST.in" [target, list]
            result `shouldBe` False
        , testProperty "LIST.in is indeterminate when an item is not present (list with opaque middle)"
            . property
            $ do
                l <- forAll smallNat
                let elems = map numDV [1 .. l]
                    list = KList Fixture.testKListDef elems $ Just ([trm| INIT:SortList |], [])
                    target = numDV 0
                result <- evalHook "LIST.in" [target, list]
                Nothing === result
        ]
  where
    x `_shouldBe_` b = Just (Builtin.boolTerm b) @=? x
    x `shouldBe` b = Just (Builtin.boolTerm b) === x

testListMakeHook :: TestTree
testListMakeHook =
    testGroup
        "LIST.make"
        [ testCase "LIST.in makes empty lists when size 0 is given" $ do
            let thing = numDV 0
                size = Builtin.intTerm 0
            result <- evalHook "LIST.make" [size, thing]
            Just (KList Builtin.kItemListDef [] Nothing) @=? result
        , testProperty "LIST.in makes a list of given length" . property $ do
            let thing = numDV 0
            size <- forAll smallNat
            let sizeTerm = Builtin.intTerm $ fromIntegral size
            result <- evalHook "LIST.make" [sizeTerm, thing]
            case result of
                Nothing -> failure
                Just (KList _ concreteElems Nothing) ->
                    concreteElems === replicate size thing
                Just _ -> failure
        ]

testListRangeHook :: TestTree
testListRangeHook =
    testGroup
        "LIST.range"
        [ testProperty "LIST.range with zero indexes is identity" . property $ do
            size <- forAll smallNat
            let list = listOfThings size
            result <- evalHook "LIST.range" [list, Builtin.intTerm 0, Builtin.intTerm 0]
            Just list === result
        , testProperty "LIST.range with valid range in concrete list" . property $ do
            size <- forAll smallNat
            a <- forAll $ between0And size
            let maxB = size - a
            b <- forAll $ between0And maxB
            let list = listOfThings size -- [1..size]
                expected =
                    KList Fixture.testKListDef (map numDV [a + 1 .. size - b]) Nothing
                aTerm = Builtin.intTerm $ fromIntegral a
                bTerm = Builtin.intTerm $ fromIntegral b
            result <- evalHook "LIST.range" [list, aTerm, bTerm]
            Just expected === result
        , testProperty "LIST.range with opaque middle but feasible range" . property $ do
            front <- forAll $ between1And 42 -- NB list must not be just the variable
            back <- forAll smallNat
            frontDrop <- forAll $ between0And front
            backDrop <- forAll $ between0And back
            let frontElems = map numDV [1..front]
                backElems = map numDV [1..back]
                midVar = [trm| MID:List |]
                list =
                    KList Fixture.testKListDef frontElems $ Just (midVar, backElems)
                frontTerm = Builtin.intTerm $ fromIntegral frontDrop
                backTerm = Builtin.intTerm $ fromIntegral backDrop
            result <- evalHook "LIST.range" [list, frontTerm, backTerm]
            let expected =
                    KList
                        Fixture.testKListDef
                        (map numDV [frontDrop + 1 .. front])
                        (Just (midVar, map numDV [1 .. back - backDrop]))
            Just expected === result
        , testProperty "LIST.range concrete list, parameters too large" . property $ do
            size <- forAll smallNat
            plus <- forAll $ between1And 42
            let zero = Builtin.intTerm 0
                tooMuch = Builtin.intTerm $ fromIntegral (size + plus)
                list = listOfThings size
            result1 <- evalHook "LIST.range" [list, zero, tooMuch]
            Nothing === result1
            result2 <- evalHook "LIST.range" [list, tooMuch, zero]
            Nothing === result2
        ]

testListSizeHook :: TestTree
testListSizeHook =
    testGroup
        "LIST.size hook"
        [ testProperty "LIST.size on concrete lists" . property $ do
            l <- forAll smallNat
            let aList =
                    KList Fixture.testKListDef (replicate l [trm| \dv{SomeSort{}}("thing")|]) Nothing
            result <- evalHook "LIST.size" [aList]
            Just (Builtin.intTerm (fromIntegral l)) === result
        , testProperty "LIST.size on symbolic lists has no result" . property $ do
            l <- forAll $ between1And 5
            let aList =
                    KList Fixture.testKListDef [] $
                        Just ([trm| INIT:SortList|], replicate l [trm| \dv{SomeSort{}}("thing")|])
            result <- evalHook "LIST.size" [aList]
            Nothing === result
        ]

testListGetHook :: TestTree
testListGetHook =
    testGroup
        "LIST.get hook"
        [ testProperty "LIST.get with empty lists has no result" . property $ do
            i <- forAll $ Gen.int (Range.constant (-42) 42)
            let iTerm = Builtin.intTerm $ fromIntegral i
            result <- evalHook "LIST.get" [aList [] Nothing, iTerm]
            Nothing === result
        , -- positive index
          testProperty "LIST.get with idx >= 0 on concrete lists" . property $ do
            l <- forAll smallNat
            i <- forAll $ between0And l
            let iTerm = Builtin.intTerm $ fromIntegral i
            result <- evalHook "LIST.get" [aList [0 .. l] Nothing, iTerm]
            Just (numDV i) === result
        , testProperty "LIST.get with idx >= 0 on list with symbolic tail" . property $ do
            l <- forAll smallNat
            i <- forAll $ between0And l
            let iTerm = Builtin.intTerm $ fromIntegral i
            result <-
                evalHook "LIST.get" [aList [0 .. l] (Just ([trm|X:SortList|], [])), iTerm]
            Just (numDV i) === result
        , testProperty "List.get with idx >= 0 where concrete head too short" . property $ do
            l <- forAll smallNat
            delta <- forAll $ between1And 42
            let iTerm = Builtin.intTerm $ fromIntegral (l + delta)
            result <-
                evalHook "LIST.get" [aList [0 .. l] Nothing, iTerm]
            result2 <-
                evalHook "LIST.get" [aList [0 .. l] (Just ([trm|X:SortList|], [])), iTerm]
            Nothing === result
            Nothing === result2
        , testProperty "LIST.get with idx >= 0 on list with symbolic head" . property $ do
            l <- forAll smallNat
            i <- forAll $ between0And l
            let symList = aList [] $ Just ([trm| X:SortList|], [0 .. l])
                iTerm = Builtin.intTerm $ fromIntegral i
            result <- evalHook "LIST.get" [symList, iTerm]
            Nothing === result
        , -- negative indexes
          testProperty "LIST.get with idx < 0 on concrete lists" . property $ do
            l <- forAll smallNat
            i <- forAll $ between1And (l + 1)
            let iTerm = Builtin.intTerm $ fromIntegral $ negate i
            result <- evalHook "LIST.get" [aList [0 .. l] Nothing, iTerm]
            Just (numDV (l + 1 - i)) === result
        , testProperty "LIST.get with idx < 0 on list with symbolic tail" . property $ do
            l <- forAll smallNat
            i <- forAll $ between1And (l + 1)
            let iTerm = Builtin.intTerm $ fromIntegral $ negate i
            result <-
                evalHook "LIST.get" [aList [0 .. l] (Just ([trm|X:SortList|], [])), iTerm]
            Nothing === result
        , testProperty "List.get with idx < 0 where concrete tail too short" . property $ do
            l <- forAll smallNat
            delta <- forAll $ between1And 42
            let iTerm = Builtin.intTerm $ fromIntegral $ negate (l + 1 + delta)
            result <-
                evalHook "LIST.get" [aList [] (Just ([trm|X:SortList|], [0 .. l])), iTerm]
            result2 <-
                evalHook "LIST.get" [aList [0 .. l] (Just ([trm|X:SortList|], [0 .. l])), iTerm]
            Nothing === result
            Nothing === result2
        , testProperty "LIST.get on list with symbolic head, concrete tail" . property $ do
            l <- forAll smallNat
            i <- forAll $ between1And (l + 1)
            let iTerm = Builtin.intTerm $ fromIntegral $ negate i
            result <-
                evalHook "LIST.get" [aList [] $ Just ([trm| X:SortList|], [0 .. l]), iTerm]
            Just (numDV (l + 1 - i)) === result
        ]
  where
    aList :: [Int] -> Maybe (Term, [Int]) -> Term
    aList heads mbTail =
        KList Fixture.testKListDef (map numDV heads) (fmap (second $ map numDV) mbTail)

testListUpdateHook :: TestTree
testListUpdateHook =
    testGroup
        "LIST.update hook"
        [ testProperty "LIST.update within concrete head of a list" . property $ do
            l <- forAll $ between1And 42
            i <- forAll $ between0And (l - 1)
            let list = listOfThings l
                thing = [trm| \dv{SomeSort}("thing") |]
            result <- evalHook "LIST.update" [list, Builtin.intTerm (fromIntegral i), thing]
            let expectedHeads = map numDV [1 .. i] <> [thing] <> map numDV [i + 2 .. l]
            Just (KList Fixture.testKListDef expectedHeads Nothing) === result
        , testProperty "LIST.update outside length of concrete head of a list" . property $ do
            l <- forAll smallNat
            i <- forAll smallNat
            let list =
                    KList Fixture.testKListDef (map numDV [1 .. l]) $
                        Just ([trm| X:SortList |], [])
                thing = [trm| \dv{SomeSort}("thing") |]
                idxTerm = Builtin.intTerm $ fromIntegral $ l + i
            result <- evalHook "LIST.update" [list, idxTerm, thing]
            Nothing === result
        ]

testMapHooks :: TestTree
testMapHooks =
    testGroup
        "MAP hooks"
        [ testMapUpdateHook
        , testMapUpdateAllHook
        , testMapRemoveHook
        , testMapSizeHook
        , testMapInKeysHook
        , testMapLookupHook
        , testMapLookupOrDefaultHook
        , testMapKeysListHook
        , testMapValuesHook
        , testMapInclusionHook
        ]

-- map helpers for property tests
genKey, genItem :: MonadGen m => m Term
genKey = dv kmapKeySort <$> Gen.utf8 (Range.singleton 3) Gen.ascii
genItem = dv kmapElementSort <$> Gen.utf8 (Range.singleton 10) Gen.ascii

genAssoc :: MonadGen m => m (Term, Term)
genAssoc = (,) <$> genKey <*> genItem

genAssocs :: MonadGen m => Range Int -> m [(Term, Term)]
genAssocs range = noDupKeys <$> Gen.list range genAssoc
  where
    noDupKeys = nubBy ((==) `on` fst)

mapWith :: [(Term, Term)] -> Maybe Term -> Term
mapWith = KMap Fixture.testKMapDefinition

testMapUpdateHook :: TestTree
testMapUpdateHook =
    testGroup
        "MAP.update hook tests"
        [ testCase "updates an empty map to a singleton" $ do
            result <- runUpdate [Fixture.emptyKMap, key, value]
            Just Fixture.concreteKMapWithOneItem @=? result
        , testCase "can add an association to a map" $ do
            result <- runUpdate [Fixture.concreteKMapWithOneItem, key2, value2]
            Just Fixture.concreteKMapWithTwoItems @=? result
        , testCase "can overwrite a value" $ do
            result <- runUpdate [Fixture.concreteKMapWithTwoItems, key2, value]
            let expected = mapWith [(key, value), (key2, value)] Nothing
            Just expected @=? result
        , testCase "can update map with symbolic rest if key present" $ do
            result <- runUpdate [Fixture.concreteKMapWithOneItemAndRest, key, value2]
            let expected = mapWith [(key, value2)] (Just restVar)
            Just expected @=? result
        , testCase "can update map with unevaluated key if key is syntactically equal" $ do
            let keyG = [trm| g{}() |]
            result <- runUpdate [Fixture.functionKMapWithOneItemAndRest, keyG, value2]
            let expected = mapWith [(keyG, value2)] (Just restVar)
            Just expected @=? result
        , testCase "cannot update map at unevaluated key if key not syntactically present" $ do
            let keyG = [trm| g{}() |]
            result <- runUpdate [Fixture.concreteKMapWithTwoItems, keyG, value2]
            Nothing @=? result
        , testCase "cannot update map with symbolic rest if key not present" $ do
            result <- runUpdate [Fixture.concreteKMapWithOneItemAndRest, key2, value2]
            Nothing @=? result
        , testCase "cannot update map if any unevaluated keys present" $ do
            result <- runUpdate [Fixture.functionKMapWithOneItem, key2, value2]
            Nothing @=? result
        , testCase "cannot update non-internalised maps" $ do
            result <- runUpdate [restVar, key, value]
            Nothing @=? result
        , testCase "arity is checked" $ do
            let assertException = assertBool "Unexpected success" . isLeft . runExcept
            assertException $ runHook "MAP.update" []
            assertException $ runHook "MAP.update" [restVar]
            assertException $ runHook "MAP.update" [restVar, key]
            assertException $ runHook "MAP.update" [restVar, key, value, key2]
        ]
  where
    runUpdate = either (fail . show) pure . runExcept . runHook "MAP.update"

    key = [trm| \dv{SortTestKMapKey{}}("key") |]
    value = [trm| \dv{SortTestKMapItem{}}("value") |]
    key2 = [trm| \dv{SortTestKMapKey{}}("key2") |]
    value2 = [trm| \dv{SortTestKMapItem{}}("value2") |]

    restVar = [trm| REST:SortTestKMap{} |]

testMapUpdateAllHook :: TestTree
testMapUpdateAllHook =
    testGroup
        "MAP.updateAll"
        [ testCase "Updating an empty map returns the update map" $ do
            result <- runUpdateAll [Fixture.emptyKMap, Fixture.functionKMapWithOneItemAndRest]
            Just Fixture.functionKMapWithOneItemAndRest @=? result
        , testCase "Updating with an empty map returns the original" $ do
            result <- runUpdateAll [Fixture.functionKMapWithOneItemAndRest, Fixture.emptyKMap]
            Just Fixture.functionKMapWithOneItemAndRest @=? result
        , testProperty "A map updated with itself remains unmodified" . property $ do
            theMap <-
                forAll $
                    Gen.element
                        [ Fixture.concreteKMapWithTwoItems
                        , Fixture.concreteKMapWithOneItemAndRest
                        , Fixture.functionKMapWithOneItemAndRest
                        ]
            result <- runUpdateAll [theMap, theMap]
            Just theMap === result
        , testCase "Cannot (non-trivially) update a map with rest" $ do
            result <-
                runUpdateAll
                    [ Fixture.functionKMapWithOneItemAndRest
                    , Fixture.concreteKMapWithTwoItems
                    ]
            Nothing @=? result
        , testCase "Cannot (non-trivially) update a map by a map with rest" $ do
            result <-
                runUpdateAll
                    [ Fixture.concreteKMapWithTwoItems
                    , Fixture.concreteKMapWithOneItemAndRest
                    ]
            Nothing @=? result
        , testCase "Cannot update a map that has symbolic keys" $ do
            result <-
                runUpdateAll
                    [ Fixture.functionKMapWithOneItem
                    , Fixture.concreteKMapWithOneItem
                    ]
            Nothing @=? result
        , testCase "Cannot update a map by a map that has symbolic keys" $ do
            result <-
                runUpdateAll
                    [ Fixture.concreteKMapWithOneItem
                    , Fixture.functionKMapWithOneItem
                    ]
            Nothing @=? result
        , testProperty "Updates using fully concrete maps work as expected" . property $ do
            original <- forAll $ genAssocs (Range.linear 0 10)
            updates <- forAll $ genAssocs (Range.linear 0 10)
            let originalWithoutUpdates = filter (not . (`Set.member` updateKeys) . fst) original
                updateKeys = Set.fromList $ map fst updates
            result <- runUpdateAll [concreteMap original, concreteMap updates]
            Just (concreteMap (originalWithoutUpdates <> updates)) === result
        ]
  where
    runUpdateAll :: MonadFail m => [Term] -> m (Maybe Term)
    runUpdateAll = either (fail . show) pure . runExcept . runHook "MAP.updateAll"

    concreteMap = flip mapWith Nothing

testMapRemoveHook :: TestTree
testMapRemoveHook =
    testGroup
        "MAP.remove"
        [ testProperty "leaves empty maps unchanged" . property $ do
            k <- forAll smallNat
            let kTerm = dv kmapKeySort $ BS.pack $ show k
            result <- runRemove [Fixture.emptyKMap, kTerm]
            Just Fixture.emptyKMap === result
        , testCase "removes a concrete key that is present" $ do
            result <- runRemove [Fixture.concreteKMapWithTwoItems, key2]
            Just Fixture.concreteKMapWithOneItem @=? result
        , testCase "leaves fully concrete maps without key to delete unchanged" $ do
            result <- runRemove [Fixture.concreteKMapWithTwoItems, key3]
            Just Fixture.concreteKMapWithTwoItems @=? result
        , testCase "can remove a key that is present from a map with rest" $ do
            let theMap =
                    mapWith [(key, value), (key2, value2)] (Just restVar)
            result <- runRemove [theMap, key2]
            Just Fixture.concreteKMapWithOneItemAndRest @=? result
        , testCase "returns rest alone when removing last known key from a map with rest" $ do
            result <- runRemove [Fixture.concreteKMapWithOneItemAndRest, key]
            Just restVar @=? result
        , testCase "can remove non-concrete keys when syntactically equal" $ do
            result <- runRemove [Fixture.functionKMapWithOneItem, [trm| g{}() |]]
            Just Fixture.emptyKMap @=? result
            result2 <- runRemove [Fixture.functionKMapWithOneItemAndRest, [trm| g{}() |]]
            Just restVar @=? result2
        , testCase "no result if removing non-concrete keys not syntactically equal" $ do
            result <- runRemove [Fixture.concreteKMapWithTwoItems, [trm| g{}() |]]
            Nothing @=? result
        , testCase "no result when map has non-concrete syntactically different keys" $ do
            result <- runRemove [Fixture.functionKMapWithOneItem, key]
            Nothing @=? result
        , testCase "no result when removing an absent key from a map with rest" $ do
            result <- runRemove [Fixture.concreteKMapWithOneItemAndRest, key2]
            Nothing @=? result
        , testCase "arity is checked" $ do
            let assertException = assertBool "Unexpected success" . isLeft . runExcept
            assertException $ runHook "MAP.remove" []
            assertException $ runHook "MAP.remove" [restVar]
            assertException $ runHook "MAP.remove" [restVar, key, key]
        ]
  where
    runRemove :: MonadFail m => [Term] -> m (Maybe Term)
    runRemove = either (fail . show) pure . runExcept . runHook "MAP.remove"

    key = [trm| \dv{SortTestKMapKey{}}("key") |]
    value = [trm| \dv{SortTestKMapItem{}}("value") |]
    key2 = [trm| \dv{SortTestKMapKey{}}("key2") |]
    value2 = [trm| \dv{SortTestKMapItem{}}("value2") |]
    key3 = [trm| \dv{SortTestKMapKey{}}("key3") |]

    restVar = [trm| REST:SortTestKMap{} |]

testMapSizeHook :: TestTree
testMapSizeHook =
    testGroup
        "MAP.size"
        [ testCase "arity is checked" $ do
            let assertException = assertBool "Unexpected success" . isLeft . runExcept
            assertException $ runHook "MAP.size" []
            assertException $ runHook "MAP.size" $ replicate 2 [trm| X:SortTestKMap |]
        , testCase "cannot determine size of a map with rest" $ do
            result <- runSize [Fixture.concreteKMapWithOneItemAndRest]
            Nothing @=? result
        , testProperty "correctly determines size of a map without rest" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 0 42)
            result <- runSize [mapWith assocs Nothing]
            Just (Builtin.intTerm (fromIntegral $ length assocs)) === result
        ]
  where
    runSize :: MonadFail m => [Term] -> m (Maybe Term)
    runSize = either (fail . show) pure . runExcept . runHook "MAP.size"

testMapLookupHook :: TestTree
testMapLookupHook =
    testGroup
        "MAP.lookup"
        [ testCase "arity is checked" $ do
            let assertException = assertBool "Unexpected success" . isLeft . runExcept
            assertException $ runHook "MAP.lookup" []
            assertException $ runHook "MAP.lookup" [[trm| X:SortTestKMap |]]
            assertException $ runHook "MAP.lookup" [[trm| X:SortTestKMap |], notAKey, notAKey]
        , testCase "returns Nothing when looking into an empty map" $ do
            result <- runLookup [Fixture.emptyKMap, notAKey]
            Nothing @=? result
        , testProperty "returns Nothing when key not found" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 0 10)
            result <- runLookup [mapWith assocs Nothing, notAKey]
            Nothing === result
            result2 <- runLookup [mapWith assocs (Just restVar), notAKey]
            Nothing === result2
        , testProperty "returns item when key found" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 1 10)
            key <- forAll $ Gen.element $ map fst assocs
            let expected = fromMaybe (error "bad key choice") $ lookup key assocs
            result <- runLookup [mapWith assocs Nothing, key]
            Just expected === result
            result2 <- runLookup [mapWith assocs (Just restVar), key]
            Just expected === result2
        , testCase "returns item for a non-evaluated key when present" $ do
            result <- runLookup [Fixture.functionKMapWithOneItemAndRest, [trm| g{}() |]]
            Just [trm| \dv{SortTestKMapItem{}}("value") |] @=? result
        , testProperty "no result for an unevaluated key not syntactically present" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 0 10)
            result <- runLookup [mapWith assocs Nothing, [trm| g{}() |]]
            Nothing === result
        , testCase "no result if map has non-evaluated keys when key not found" $ do
            result <- runLookup [Fixture.functionKMapWithOneItem, notAKey]
            Nothing @=? result
        ]
  where
    runLookup :: MonadFail m => [Term] -> m (Maybe Term)
    runLookup = either (fail . show) pure . runExcept . runHook "MAP.lookup"

    notAKey = [trm| \dv{SortTestKMapKey{}}("too-long-to-be-a-key") |]
    -- keys generated by genKey are 3 characters long

    restVar = [trm| REST:SortTestKMap{} |]

testMapLookupOrDefaultHook :: TestTree
testMapLookupOrDefaultHook =
    testGroup
        "MAP.lookupOrDefault"
        [ testCase "arity is checked" $ do
            let assertException = assertBool "Unexpected success" . isLeft . runExcept
            assertException $ runHook "MAP.lookupOrDefault" []
            assertException $ runHook "MAP.lookupOrDefault" [restVar]
            assertException $ runHook "MAP.lookupOrDefault" [restVar, notAKey]
            assertException $ runHook "MAP.lookupOrDefault" [restVar, notAKey, defItem, defItem]
        , testCase "returns default item when looking into an empty map" $ do
            result <- runLookup [Fixture.emptyKMap, notAKey, defItem]
            Just defItem @=? result
        , testProperty "returns default item when key not found in concrete map" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 0 10)
            result <- runLookup [mapWith assocs Nothing, notAKey, defItem]
            Just defItem === result
        , testProperty "no result when key not found in map with rest" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 0 10)
            result2 <- runLookup [mapWith assocs (Just restVar), notAKey, defItem]
            Nothing === result2
        , testProperty "returns item when key found" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 1 10)
            key <- forAll $ Gen.element $ map fst assocs
            let expected = fromMaybe (error "bad key choice") $ lookup key assocs
            result <- runLookup [mapWith assocs Nothing, key, defItem]
            Just expected === result
            result2 <- runLookup [mapWith assocs (Just restVar), key, defItem]
            Just expected === result2
        , testCase "returns item for a non-evaluated key when present" $ do
            result <- runLookup [Fixture.functionKMapWithOneItemAndRest, [trm| g{}() |], defItem]
            Just [trm| \dv{SortTestKMapItem{}}("value") |] @=? result
        , testProperty "no result for an unevaluated key not syntactically present" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 0 10)
            result <- runLookup [mapWith assocs Nothing, [trm| g{}() |], defItem]
            Nothing === result
        , testCase "no result if map has non-evaluated keys and key not found" $ do
            result <- runLookup [Fixture.functionKMapWithOneItemAndRest, notAKey, defItem]
            Nothing @=? result
        ]
  where
    runLookup :: MonadFail m => [Term] -> m (Maybe Term)
    runLookup = either (fail . show) pure . runExcept . runHook "MAP.lookupOrDefault"

    notAKey = [trm| \dv{SortTestKMapKey{}}("too-long-to-be-a-key") |]
    -- keys generated by genKey are 3 characters long
    defItem = [trm| \dv{SortTestKMapItem{}}("default") |]

    restVar = [trm| REST:SortTestKMap{} |]

testMapInKeysHook :: TestTree
testMapInKeysHook =
    testGroup
        "MAP.inKeys"
        [ testCase "arity is checked" $ do
            let assertException = assertBool "Unexpected success" . isLeft . runExcept
            assertException $ runHook "MAP.in_keys" []
            assertException $ runHook "MAP.in_keys" [notAKey]
            assertException $ runHook "MAP.in_keys" [notAKey, restVar, restVar]
        , testProperty "returns false when key not in fully-concrete map" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 0 42)
            result <- runInKeys [notAKey, mapWith assocs Nothing]
            Just (Builtin.boolTerm False) === result
        , testProperty "no result when key not present and map has rest" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 0 42)
            result <- runInKeys [notAKey, mapWith assocs (Just restVar)]
            Nothing === result
        , testProperty "returns true when key present (rest or not)" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 1 42)
            key <- forAll $ Gen.element $ map fst assocs
            result <- runInKeys [key, mapWith assocs Nothing]
            Just (Builtin.boolTerm True) === result
            result2 <- runInKeys [key, mapWith assocs (Just restVar)]
            Just (Builtin.boolTerm True) === result2
        , testCase "returns true when key syntactically present" $ do
            result <- runInKeys [[trm| g{}() |], Fixture.functionKMapWithOneItem]
            Just (Builtin.boolTerm True) @=? result
            result2 <- runInKeys [[trm| g{}() |], Fixture.functionKMapWithOneItemAndRest]
            Just (Builtin.boolTerm True) @=? result2
        , testCase "no result if unevaluated map keys present" $ do
            result <- runInKeys [notAKey, Fixture.functionKMapWithOneItem]
            Nothing @=? result
            result2 <- runInKeys [notAKey, Fixture.functionKMapWithOneItemAndRest]
            Nothing @=? result2
        , testProperty "no result for an unevaluated key not present" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 0 42)
            result <- runInKeys [[trm| g{}() |], mapWith assocs Nothing]
            Nothing === result
        ]
  where
    runInKeys :: MonadFail m => [Term] -> m (Maybe Term)
    runInKeys = either (fail . show) pure . runExcept . runHook "MAP.in_keys"

    notAKey = [trm| \dv{SortTestKMapKey{}}("too-long-to-be-a-key") |]
    -- keys generated by genKey are 3 characters long

    restVar = [trm| REST:SortTestKMap{} |]

testMapKeysListHook :: TestTree
testMapKeysListHook =
    testGroup
        "MAP.keysList"
        [ testCase "arity is checked" $ do
            let assertException = assertBool "Unexpected success" . isLeft . runExcept
            assertException $ runHook "MAP.keys_list" []
            assertException $ runHook "MAP.keys_list" [restVar, restVar]
        , testProperty "no result if map has rest" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 0 10)
            result <- runKeysList [mapWith assocs (Just restVar)]
            Nothing === result
        , testProperty "returns all keys for maps without rest" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 0 10)
            result <- runKeysList [mapWith assocs Nothing]
            let expected =
                    -- map assocs are sorted and deduplicated
                    kitemList . map fst . Set.toAscList . Set.fromList $ assocs
            Just expected === result
        ]
  where
    runKeysList :: MonadFail m => [Term] -> m (Maybe Term)
    runKeysList = either (fail . show) pure . runExcept . runHook "MAP.keys_list"

    restVar = [trm| REST:SortTestKMap{} |]

testMapValuesHook :: TestTree
testMapValuesHook =
    testGroup
        "MAP.values"
        [ testCase "arity is checked" $ do
            let assertException = assertBool "Unexpected success" . isLeft . runExcept
            assertException $ runHook "MAP.values" []
            assertException $ runHook "MAP.values" [restVar, restVar]
        , testProperty "no result if map has rest" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 0 10)
            result <- runValues [mapWith assocs (Just restVar)]
            Nothing === result
        , testProperty "returns all values for maps without rest" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 0 10)
            result <- runValues [mapWith assocs Nothing]
            let expected =
                    -- map assocs are sorted and deduplicated
                    kitemList . map snd . Set.toAscList . Set.fromList $ assocs
            Just expected === result
        ]
  where
    runValues :: MonadFail m => [Term] -> m (Maybe Term)
    runValues = either (fail . show) pure . runExcept . runHook "MAP.values"

    restVar = [trm| REST:SortTestKMap{} |]

testMapInclusionHook :: TestTree
testMapInclusionHook =
    testGroup
        "MAP.inclusion"
        [ testCase "arity is checked" $ do
            let assertException = assertBool "Unexpected success" . isLeft . runExcept
            assertException $ runHook "MAP.inclusion" []
            assertException $ runHook "MAP.inclusion" [restVar]
            assertException $ runHook "MAP.inclusion" [restVar, restVar, restVar]
        , testProperty "returns true if two argument maps are identical" . property $ do
            theMap <- forAll anyMap
            result <- runInclusion [theMap, theMap]
            Just (Builtin.boolTerm True) === result
        , testProperty "an empty map is included in any map" . property $ do
            theMap <- forAll anyMap
            result <- runInclusion [Fixture.emptyKMap, theMap]
            Just (Builtin.boolTerm True) === result
        , testProperty "no result if maps differ and the first one has a rest" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 1 10)
            result <-
                runInclusion
                    [ mapWith assocs (Just restVar)
                    , mapWith ((key, value) : assocs) Nothing
                    ]
            Nothing === result
            result2 <-
                runInclusion
                    [ mapWith assocs (Just restVar)
                    , mapWith ((key, value) : assocs) (Just restVar)
                    ]
            Nothing === result2
        , testProperty "returns true if 1st map without rest included in 2nd" . property $ do
            assocs <- forAll $ genAssocs (Range.linear 1 10)
            result <-
                runInclusion
                    [ mapWith assocs Nothing
                    , mapWith ((key, value) : assocs) Nothing
                    ]
            Just (Builtin.boolTerm True) === result
            result2 <-
                runInclusion
                    [ mapWith assocs Nothing
                    , mapWith ((key, value) : assocs) (Just restVar)
                    ]
            Just (Builtin.boolTerm True) === result2
        , testProperty
            "returns false if 1st map without rest not included in 2nd without rest"
            . property
            $ do
                assocs <- forAll $ genAssocs (Range.linear 1 10)
                result <-
                    runInclusion
                        [ mapWith ((key, value) : assocs) Nothing
                        , mapWith assocs Nothing
                        ]
                Just (Builtin.boolTerm False) === result
        , testProperty
            "no result if 1st map without rest not included in 2nd with rest"
            . property
            $ do
                assocs <- forAll $ genAssocs (Range.linear 1 10)
                result2 <-
                    runInclusion
                        [ mapWith ((key, value) : assocs) Nothing
                        , mapWith assocs (Just restVar)
                        ]
                Nothing === result2
        ]
  where
    runInclusion :: MonadFail m => [Term] -> m (Maybe Term)
    runInclusion = either (fail . show) pure . runExcept . runHook "MAP.inclusion"

    restVar = [trm| REST:SortTestKMap{} |]

    key = [trm| \dv{SortTestKMapKey{}}("new key") |]
    -- NB longer than generated ones!
    value = [trm| \dv{SortTestKMapItem{}}("value") |]

    anyMap = do
        assocs <- genAssocs (Range.linear 0 10)
        Gen.element
            [ Fixture.emptyKMap
            , Fixture.concreteKMapWithOneItem
            , Fixture.concreteKMapWithTwoItems
            , Fixture.concreteKMapWithOneItemAndRest
            , Fixture.concreteKeySymbolicValueKMapWithRest
            , Fixture.symbolicKMapWithOneItem
            , Fixture.symbolicKMapWithTwoItems
            , Fixture.concreteAndSymbolicKMapWithTwoItems
            , Fixture.functionKMapWithOneItemAndRest
            , Fixture.functionKMapWithOneItem
            , mapWith assocs (Just restVar)
            ]

------------------------------------------------------------
-- helpers
runHook :: BS.ByteString -> Builtin.BuiltinFunction
runHook name =
    fromMaybe (error $ show name <> " hook not found") $
        Map.lookup name Builtin.hooks

evalHook :: MonadFail m => BS.ByteString -> [Term] -> m (Maybe Term)
evalHook name args = either (fail . show) pure $ runExcept $ runHook name args

smallNat :: Gen Int
smallNat = Gen.int (Range.linear 0 42)

between0And :: Int -> Gen Int
between0And n -- assuming n >= 0
    | n >= 0 = Gen.int (Range.linear 0 n)
    | otherwise = error $ "Unexpected request for number between 0 and " <> show n

between1And :: Int -> Gen Int
between1And n -- assuming n > 0!
    | n > 0 = Gen.int (Range.linear 1 n)
    | otherwise = error $ "Unexpected request for number between 1 and " <> show n
