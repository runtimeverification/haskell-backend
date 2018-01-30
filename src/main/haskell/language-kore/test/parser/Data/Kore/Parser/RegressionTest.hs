module Data.Kore.Parser.RegressionTest (regressionTests, regressionTestsInputFiles) where

import           Test.Tasty
import           Test.Tasty.Golden

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

prettyPrint :: Either String Definition -> LazyByteString.ByteString
prettyPrint (Left err) =
    LazyChar8.pack ("Parse error: " ++ err ++ ".")
prettyPrint (Right definition) =
    LazyChar8.pack (show definition)

runParser :: String -> IO LazyByteString.ByteString
runParser inputFileName = do
    fileContent <- ByteString.readFile inputFileName
    return (prettyPrint (fromKore fileContent))
