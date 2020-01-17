module Test.SQL
    ( testTable
    ) where

import Test.Tasty

import qualified Database.SQLite.Simple as SQLite

import SQL

import Test.Tasty.HUnit.Ext

testTable :: forall table. Table table => [table] -> TestTree
testTable rows =
    testCase "" $ withTestConnection $ \conn -> do
        -- create the table
        createTable conn (Proxy @table)
        -- insert (unique) rows
        keys1 <- traverse (insertUniqueRow conn) rows
        -- select the rows which were just inserted
        keys2 <- traverse (selectRow conn) rows
        -- assert that the inserted and selected keys are the same
        assertEqual "expected to select inserted keys" (Just <$> keys1) keys2

withTestConnection :: (Connection -> IO a) -> IO a
withTestConnection = SQLite.withConnection ":memory:"
