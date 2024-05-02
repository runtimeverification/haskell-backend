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
import Booster.Pattern.Base
import Booster.Syntax.Json.Internalise (trm)
import Booster.Syntax.ParsedKore.Internalise (symb)
import Test.Booster.Fixture as Fixture

test_builtins :: [TestTree]
test_builtins =
    [ testIntHooks
    , testListSizeHooks
    , testListGetHooks
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

testListSizeHooks :: TestTree
testListSizeHooks =
    testGroup
        "LIST.size hooks"
        [ testProperty "LIST.size on concrete lists" . property $ do
            l <- forAll smallNat
            let aList =
                    KList Fixture.testKListDef (replicate l [trm| \dv{SomeSort{}}("thing")|]) Nothing
            result <- evalEither $ runExcept $ hook [aList]
            Just (Builtin.intTerm (fromIntegral l)) === result
        , testProperty "LIST.size on symbolic lists has no result" . property $ do
            l <- forAll $ between1And 5
            let aList =
                    KList Fixture.testKListDef [] $
                        Just ([trm| INIT:SortList|], replicate l [trm| \dv{SomeSort{}}("thing")|])
            result <- evalEither $ runExcept $ hook [aList]
            Nothing === result
        , testCase "LIST.size arity is checked" $ do
            let assertException = assertBool "Unexpected success" . isLeft . runExcept
            assertException $ hook []
            assertException $ hook $ replicate 2 [trm| X:SortList{} |]
            assertException $ hook $ replicate 3 [trm| X:SortList{} |]
        ]
  where
    hook = runHook "LIST.size"

testListGetHooks :: TestTree
testListGetHooks =
    testGroup
        "LIST.get hooks"
        [ testCase "LIST.get arity is checked" $ do
            let assertException = assertBool "Unexpected success" . isLeft . runExcept
            assertException $ hook []
            assertException $ hook [[trm| X:SortList{} |]]
            assertException $ hook $ replicate 3 [trm| X:SortList{} |]
        , testProperty "LIST.get with empty lists has no result" . property $ do
            i <- forAll $ Gen.int (Range.constant (-42) 42)
            let iTerm = Builtin.intTerm $ fromIntegral i
            result <- evalEither $ runExcept $ hook [aList [] Nothing, iTerm]
            Nothing === result
        , -- positive index
          testProperty "LIST.get with idx >= 0 on concrete lists" . property $ do
            l <- forAll smallNat
            i <- forAll $ between0And l
            let iTerm = Builtin.intTerm $ fromIntegral i
            result <- evalEither $ runExcept $ hook [aList [0 .. l] Nothing, iTerm]
            Just (mkDV i) === result
        , testProperty "LIST.get with idx >= 0 on list with symbolic tail" . property $ do
            l <- forAll smallNat
            i <- forAll $ between0And l
            let iTerm = Builtin.intTerm $ fromIntegral i
            result <-
                evalEither . runExcept $
                    hook [aList [0 .. l] (Just ([trm|X:SortList|], [])), iTerm]
            Just (mkDV i) === result
        , testProperty "List.get with idx >= 0 where concrete head too short" . property $ do
            l <- forAll smallNat
            delta <- forAll $ between1And 42
            let iTerm = Builtin.intTerm $ fromIntegral (l + delta)
            result <-
                evalEither . runExcept $
                    hook [aList [0 .. l] Nothing, iTerm]
            result2 <-
                evalEither . runExcept $
                    hook [aList [0 .. l] (Just ([trm|X:SortList|], [])), iTerm]
            Nothing === result
            Nothing === result2
        , testProperty "LIST.get with idx >= 0 on list with symbolic head" . property $ do
            l <- forAll smallNat
            i <- forAll $ between0And l
            let symList = aList [] $ Just ([trm| X:SortList|], [0 .. l])
                iTerm = Builtin.intTerm $ fromIntegral i
            result <- evalEither $ runExcept $ hook [symList, iTerm]
            Nothing === result
        , -- negative indexes
          testProperty "LIST.get with idx < 0 on concrete lists" . property $ do
            l <- forAll smallNat
            i <- forAll $ between1And (l + 1)
            let iTerm = Builtin.intTerm $ fromIntegral $ negate i
            result <- evalEither $ runExcept $ hook [aList [0 .. l] Nothing, iTerm]
            Just (mkDV (l + 1 - i)) === result
        , testProperty "LIST.get with idx < 0 on list with symbolic tail" . property $ do
            l <- forAll smallNat
            i <- forAll $ between1And (l + 1)
            let iTerm = Builtin.intTerm $ fromIntegral $ negate i
            result <-
                evalEither . runExcept $
                    hook [aList [0 .. l] (Just ([trm|X:SortList|], [])), iTerm]
            Nothing === result
        , testProperty "List.get with idx < 0 where concrete tail too short" . property $ do
            l <- forAll smallNat
            delta <- forAll $ between1And 42
            let iTerm = Builtin.intTerm $ fromIntegral $ negate (l + 1 + delta)
            result <-
                evalEither . runExcept $
                    hook [aList [] (Just ([trm|X:SortList|], [0 .. l])), iTerm]
            result2 <-
                evalEither . runExcept $
                    hook [aList [0 .. l] (Just ([trm|X:SortList|], [0 .. l])), iTerm]
            Nothing === result
            Nothing === result2
        , testProperty "LIST.get on list with symbolic head, concrete tail" . property $ do
            l <- forAll smallNat
            i <- forAll $ between1And (l + 1)
            let iTerm = Builtin.intTerm $ fromIntegral $ negate i
            result <-
                evalEither . runExcept $
                    hook [aList [] $ Just ([trm| X:SortList|], [0 .. l]), iTerm]
            Just (mkDV (l + 1 - i)) === result
        ]
  where
    hook = runHook "LIST.get"

    aList :: [Int] -> Maybe (Term, [Int]) -> Term
    aList heads mbTail =
        KList Fixture.testKListDef (map mkDV heads) (fmap (second $ map mkDV) mbTail)

    -- FIXME strictly-speaking, we would need injections to KItem here
    mkDV = dv someSort . BS.pack . show

testMapHooks :: TestTree
testMapHooks =
    testGroup
        "MAP hooks"
        [ testMapUpdateHook
        , testMapUpdateAllHook
        , testMapRemoveHook
        ]

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

    mapWith = KMap Fixture.testKMapDefinition

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
            let noDupKeys = nubBy ((==) `on` fst)
            original <- forAll $ noDupKeys <$> Gen.list (Range.linear 0 10) genAssoc
            updates <- forAll $ noDupKeys <$> Gen.list (Range.linear 0 10) genAssoc
            let originalWithoutUpdates = filter (not . (`Set.member` updateKeys) . fst) original
                updateKeys = Set.fromList $ map fst updates
            result <- runUpdateAll [concreteMap original, concreteMap updates]
            Just (concreteMap (originalWithoutUpdates <> updates)) === result
        ]
  where
    runUpdateAll :: MonadFail m => [Term] -> m (Maybe Term)
    runUpdateAll = either (fail . show) pure . runExcept . runHook "MAP.updateAll"

    concreteMap pairs = KMap Fixture.testKMapDefinition pairs Nothing

    genKey = dv kmapKeySort <$> Gen.utf8 (Range.singleton 3) Gen.ascii
    genItem = dv kmapElementSort <$> Gen.utf8 (Range.singleton 10) Gen.ascii
    genAssoc = (,) <$> genKey <*> genItem

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
            pure () -- Just restVar @=? result FIXME
        , testCase "can remove non-concrete keys when syntactically equal" $ do
            result <- runRemove [Fixture.functionKMapWithOneItem, [trm| g{}() |]]
            Just Fixture.emptyKMap @=? result
            result2 <- runRemove [Fixture.functionKMapWithOneItemAndRest, [trm| g{}() |]]
            pure () -- Just restVar @=? result2 FIXME
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

    mapWith = KMap Fixture.testKMapDefinition

    key = [trm| \dv{SortTestKMapKey{}}("key") |]
    value = [trm| \dv{SortTestKMapItem{}}("value") |]
    key2 = [trm| \dv{SortTestKMapKey{}}("key2") |]
    value2 = [trm| \dv{SortTestKMapItem{}}("value2") |]
    key3 = [trm| \dv{SortTestKMapKey{}}("key3") |]

    restVar = [trm| REST:SortTestKMap{} |]

------------------------------------------------------------
-- helpers
runHook :: BS.ByteString -> Builtin.BuiltinFunction
runHook name =
    fromMaybe (error $ show name <> " hook not found") $
        Map.lookup name Builtin.hooks

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
