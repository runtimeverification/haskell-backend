module Data.Kore.Parser.RegressionTest ( InputFileName (..)
                                       , GoldenFileName (..)
                                       , regressionTest
                                       , regressionTests
                                       , regressionTestsInputFiles) where

import           Test.Tasty                 (TestTree, testGroup)
import           Test.Tasty.Golden          (findByExtension, goldenVsString)

import           Data.Kore.ASTPrettyPrint
import           Data.Kore.Parser.Parser

import qualified Data.ByteString.Lazy       as LazyByteString
import qualified Data.ByteString.Lazy.Char8 as LazyChar8
import           System.FilePath            (addExtension, splitFileName, (</>))

newtype InputFileName = InputFileName FilePath
newtype GoldenFileName = GoldenFileName FilePath

regressionTests :: [InputFileName] -> TestTree
regressionTests inputFiles =
    testGroup "Regression tests"
        (map regressionTestFromInputFile inputFiles)

regressionTestsInputFiles :: String -> IO [InputFileName]
regressionTestsInputFiles dir = do
    files <- findByExtension [".kore"] dir
    return (map InputFileName files)

regressionTestFromInputFile :: InputFileName -> TestTree
regressionTestFromInputFile inputFileName =
    regressionTest inputFileName (goldenFromInputFileName inputFileName)

regressionTest :: InputFileName -> GoldenFileName -> TestTree
regressionTest (InputFileName inputFileName) (GoldenFileName goldenFileName) =
    goldenVsString
        ("Testing '" ++ inputFileName ++ "'")
        goldenFileName
        (runParser inputFileName)

goldenFromInputFileName :: InputFileName -> GoldenFileName
goldenFromInputFileName (InputFileName inputFile) =
    GoldenFileName
        (directory </> "expected" </> addExtension fileName ".golden")
  where (directory, fileName) = splitFileName inputFile

toByteString :: Either String Definition -> LazyByteString.ByteString
toByteString (Left err) =
    LazyChar8.pack ("Parse error: " ++ err ++ ".")
toByteString (Right definition) =
    LazyChar8.pack (prettyPrintToString definition)

runParser :: String -> IO LazyByteString.ByteString
runParser inputFileName = do
    fileContent <- readFile inputFileName
    return (toByteString (fromKore inputFileName fileContent))
