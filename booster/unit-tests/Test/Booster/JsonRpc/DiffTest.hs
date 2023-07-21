{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.JsonRpc.DiffTest (
    test_jsonDiff,
) where

import Data.ByteString.Lazy.Char8 qualified as BS
import System.FilePath
import Test.Tasty
import Test.Tasty.Golden (findByExtension)
import Test.Tasty.HUnit

import Booster.JsonRpc.Utils
import Kore.JsonRpc.Types (APIMethod (..))
import Test.Booster.Util (testGoldenVsString)

testDataDir :: FilePath
testDataDir = "test/jsonrpc-examples"

typeExtensions :: [BS.ByteString]
typeExtensions =
    ".error"
        : ".random.json"
        : ".kore.json"
        : ".error.response"
        : [ "." <> kind <> "." <> reqOrRes
          | kind <- ["execute", "implies", "simplify", "add-module", "get-model"]
          , reqOrRes <- ["request", "response"]
          ]

isTestFile :: FilePath -> Bool
isTestFile f =
    let f' = BS.pack f
        expectedDir = BS.pack $ testDataDir </> "expected"
     in not (expectedDir `BS.isPrefixOf` f')
            && any (`BS.isSuffixOf` f') typeExtensions

typeFromExtension :: FilePath -> KoreRpcType
typeFromExtension name
    | ".request" == ext = RpcReq $ readMethod kind
    | ".response" == ext, ".error" == kind = RpcErr
    | ".response" == ext = RpcResp $ readMethod kind
    | ".error" == ext = NotRpcJs
    | ".json" == ext, ".kore" == kind = RpcKore
    | ".json" == ext, ".random" == kind = RpcJs
    | otherwise = error $ "unexpected file name " <> takeFileName name
  where
    (name1, ext) = splitExtension name
    kind = takeExtension name1

    readMethod = \case
        ".execute" -> ExecuteM
        ".implies" -> ImpliesM
        ".simplify" -> SimplifyM
        ".add-module" -> AddModuleM
        ".get-model" -> GetModelM
        other -> error $ other <> ": No such API method"

test_jsonDiff :: IO TestTree
test_jsonDiff = do
    testFiles <-
        filter isTestFile
            <$> findByExtension [".error", ".json", ".request", ".response"] testDataDir
    let classifications =
            testGroup "Classify JSON files by their type in kore-rpc-types" $
                map classifyTest testFiles
        comparisons =
            testGroup "Pairwise comparison, expected results in files" $
                [compareTest f1 f2 | f1 <- testFiles, f2 <- testFiles, f1 /= f2]
    pure $ testGroup "JSON diff tool tests" [classifications, comparisons]
  where
    classifyTest f = testCase ("Classify " <> takeFileName f) $ do
        fileType <- rpcTypeOf . decodeKoreRpc <$> BS.readFile f
        fileType @?= typeFromExtension f
    compareTest f1 f2 = do
        let expectedName =
                testDataDir </> "expected" </> takeFileName f1 <> "@" <> takeFileName f2
            renderedDiff = renderResult f1 f2 <$> diffJson f1 f2
            testName =
                takeFileName f1 <> " vs " <> takeFileName f2
        testGoldenVsString testName expectedName renderedDiff
