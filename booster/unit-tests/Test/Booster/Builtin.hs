{-# LANGUAGE QuasiQuotes #-}

{- |
Copyright   : (c) Runtime Verification, 2024
License     : BSD-3-Clause
-}
module Test.Booster.Builtin (
    test_builtins,
) where

import Control.Monad.Trans.Except
import Data.Either (isLeft)
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)
import Data.Text qualified as Text

import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Test.Tasty (TestTree, testGroup)
import Test.Tasty.HUnit hiding (assert)
import Test.Tasty.Hedgehog

import Booster.Builtin qualified as Builtin (hooks)
import Booster.Builtin.BOOL qualified as Builtin
import Booster.Builtin.INT qualified as Builtin
import Booster.Pattern.Base
import Booster.Syntax.Json.Internalise (trm)
import Booster.Syntax.ParsedKore.Internalise (symb)
import Test.Booster.Fixture as Fixture

test_builtins :: [TestTree]
test_builtins =
    [ testIntHooks
    , testListSizeHooks
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
            let f =
                    fromMaybe
                        (error $ "Hook " <> show name <> " missing")
                        (Map.lookup name Builtin.hooks)
                runHook h args = either (error . Text.unpack) id . runExcept $ h args
            a <- fmap fromIntegral $ forAll $ Gen.int64 Range.linearBounded
            b <- fmap fromIntegral $ forAll $ Gen.int64 Range.linearBounded
            let dv_a = Builtin.intTerm a
                dv_b = Builtin.intTerm b
            -- regular computation
            Just (result $ op a b) === runHook f [dv_a, dv_b]
            -- Nothing for unevaluated arguments
            let fct = [symb| symbol f{}(SortInt) : SortInt [function{}()] |]
            Nothing === runHook f [app fct [dv_a], dv_b]
            Nothing === runHook f [dv_a, app fct [dv_b]]
            Nothing === runHook f [app fct [dv_a], app fct [dv_b]]
            -- arity error on wrong argument count
            let assertException = assert . isLeft . runExcept
            assertException $ f []
            assertException $ f [dv_a]
            assertException $ f [dv_a, dv_a, dv_a]

testListSizeHooks :: TestTree
testListSizeHooks =
    testGroup
        "LIST.size hooks"
        [ testProperty "LIST.size on concrete lists works" . property $ do
            l <- forAll $ Gen.int (Range.constant 0 12)
            let aList =
                    KList Fixture.testKListDef (replicate l [trm| \dv{SomeSort{}}("thing")|]) Nothing
            hook <- maybe failure pure $ Map.lookup "LIST.size" Builtin.hooks
            result <- evalEither $ runExcept $ hook [aList]
            Just (Builtin.intTerm (fromIntegral l)) === result
        , testProperty "LIST.size on symbolic lists has no result" . property $ do
            l <- forAll $ Gen.int (Range.constant 1 5)
            let aList =
                    KList Fixture.testKListDef [] $
                        Just ([trm| INIT:SortList|], replicate l [trm| \dv{SomeSort{}}("thing")|])
            hook <- maybe failure pure $ Map.lookup "LIST.size" Builtin.hooks
            result <- evalEither $ runExcept $ hook [aList]
            Nothing === result
        , testCase "LIST.size arity is checked" $ do
            hook <- maybe (error "LIST.size hook not found") pure $ Map.lookup "LIST.size" Builtin.hooks
            let assertException = assertBool "Unexpected success" . isLeft . runExcept
            assertException $ hook []
            assertException $ hook $ replicate 2 [trm| X:SortList{} |]
        ]
