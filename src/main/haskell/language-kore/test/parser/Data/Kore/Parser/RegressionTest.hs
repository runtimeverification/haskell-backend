module Data.Kore.Parser.RegressionTest (regressionTests, regressionTestsInputFiles) where

import           Test.Tasty                 (TestTree, testGroup)
import           Test.Tasty.Golden          (findByExtension, goldenVsString)

import           Data.Kore.ASTPrettyPrint
import           Data.Kore.Parser.Parser

import qualified Data.ByteString            as ByteString
import qualified Data.ByteString.Char8      as Char8
import qualified Data.ByteString.Lazy       as LazyByteString
import qualified Data.ByteString.Lazy.Char8 as LazyChar8
import           System.FilePath            (addExtension, splitFileName, (</>))

regressionTests :: [String] -> TestTree
regressionTests inputFiles =
    testGroup "Regression tests"
        (map regressionTest inputFiles)

regressionTestsInputFiles :: String -> IO [String]
regressionTestsInputFiles = findByExtension [".kore"]

regressionTest :: String -> TestTree
regressionTest inputFileName =
    goldenVsString
        ("Testing '" ++ inputFileName ++ "'")
        (goldenFromInputFileName inputFileName)
        (runParser inputFileName)

goldenFromInputFileName :: FilePath -> FilePath
goldenFromInputFileName inputFile =
    directory </> "expected" </> addExtension fileName ".golden"
  where (directory, fileName) = splitFileName inputFile

toByteString :: Either String Definition -> LazyByteString.ByteString
toByteString (Left err) =
    LazyChar8.pack ("Parse error: " ++ err ++ ".")
toByteString (Right definition) =
    LazyChar8.pack (prettyPrintToString definition)

runParser :: String -> IO LazyByteString.ByteString
runParser inputFileName = do
    fileContent <- ByteString.readFile inputFileName
    return (toByteString (fromKore fileContent))
