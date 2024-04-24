{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Test.Booster.Util (
    gitDiff,
    testGoldenVsString,
    testGoldenVsFile,
) where

import Data.ByteString.Lazy (ByteString)
import Test.Tasty
import Test.Tasty.Golden

gitDiff :: FilePath -> FilePath -> [String]
gitDiff ref new =
    ["git", "diff", "--no-index", "--color-words=.", ref, new]

testGoldenVsString :: TestName -> FilePath -> IO ByteString -> TestTree
testGoldenVsString name = goldenVsStringDiff name gitDiff

testGoldenVsFile :: TestName -> FilePath -> FilePath -> IO () -> TestTree
testGoldenVsFile name = goldenVsFileDiff name gitDiff
