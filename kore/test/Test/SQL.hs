module Test.SQL
    ( testTable
    ) where

import Test.Tasty

import SQL

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
