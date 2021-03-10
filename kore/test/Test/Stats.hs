module Test.Stats (test_Stats) where

import Prelude.Kore

import Test.Tasty

import System.IO (
    hClose,
 )
import System.IO.Temp

import Stats

import Test.Tasty.HUnit.Ext

test_Stats :: [TestTree]
test_Stats =
    [ testCase "read back what we wrote" $ do
        original <- getStats
        let roundtrip filePath hndl = do
                hClose hndl
                writeStats filePath original
                readStats filePath
        reread <- withSystemTempFile "kore-test-Test-Stats-.json" roundtrip
        assertEqual "expected same stats" original reread
    ]
