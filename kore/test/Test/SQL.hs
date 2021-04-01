{-# LANGUAGE Strict #-}
module Test.SQL (
    testTable,
    test_Unit,
    test_Either,
    test_Maybe,
    test_List,
    test_NonEmpty,
) where

import Data.Int (
    Int64,
 )
import Prelude.Kore
import SQL
import Test.Tasty
import Test.Tasty.HUnit.Ext

testTable :: forall table. Table table => [table] -> TestTree
testTable rows =
    testCase "" . runTestSQL $ do
        -- create the table
        createTable (Proxy @table)
        -- insert (unique) rows
        keys1 <- traverse insertUniqueRow rows
        -- select the rows which were just inserted
        keys2 <- traverse selectRow rows
        -- assert that the inserted and selected keys are the same
        assertEqual "expected to select inserted keys" (Just <$> keys1) keys2

runTestSQL :: SQL a -> IO a
runTestSQL = runSQL ":memory:"

test_Either :: TestTree
test_Either =
    testTable @(Either Int64 Int64)
        [ Left 0
        , Right 1
        , Right 2
        ]

test_Unit :: TestTree
test_Unit = testTable [()]

test_Maybe :: TestTree
test_Maybe =
    testTable @(Maybe Int64)
        [ Just 0
        , Just 1
        , Just 2
        , Nothing
        ]

test_List :: TestTree
test_List =
    testTable @[Int64]
        [ []
        , [0]
        , [0, 1]
        , [0, 1, 2]
        , [1, 2, 4, 8]
        ]

test_NonEmpty :: TestTree
test_NonEmpty =
    testTable @(NonEmpty Int64)
        [ 0 :| []
        , 0 :| [1]
        , 0 :| [1, 2]
        , 1 :| [2, 4, 8]
        ]
