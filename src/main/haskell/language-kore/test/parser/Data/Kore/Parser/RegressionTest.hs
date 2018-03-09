module Data.Kore.Parser.RegressionTest ( InputFileName (..)
                                       , GoldenFileName (..)
                                       , regressionTest
                                       , regressionTests
                                       , regressionTestsInputFiles
                                       , VerifyRequest(..)) where

import           Test.Tasty                               (TestTree, testGroup)
import           Test.Tasty.Golden                        (findByExtension,
                                                           goldenVsString)

import           Data.Kore.ASTPrettyPrint
import           Data.Kore.ASTVerifier.DefinitionVerifier
import           Data.Kore.Error
import           Data.Kore.Parser.Parser

import qualified Data.ByteString.Lazy       as LazyByteString
import qualified Data.ByteString.Lazy.Char8 as LazyChar8
import           System.FilePath            (addExtension, splitFileName, (</>))

newtype InputFileName = InputFileName FilePath
newtype GoldenFileName = GoldenFileName FilePath

data VerifyRequest = VerifyRequestYes | VerifyRequestNo

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
    regressionTest
        inputFileName
        (goldenFromInputFileName inputFileName)
        VerifyRequestYes

regressionTest :: InputFileName -> GoldenFileName -> VerifyRequest -> TestTree
regressionTest
    (InputFileName inputFileName)
    (GoldenFileName goldenFileName)
    verifyRequest
  =
    goldenVsString
        ("Testing '" ++ inputFileName ++ "'")
        goldenFileName
        (runParser inputFileName verifyRequest)

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

verify :: Either String Definition -> Either String Definition
verify (Left err) = Left err
verify (Right definition) =
    case verifyDefinition definition of
        Left e  -> Left (printError e)
        Right _ -> Right definition

runParser :: String -> VerifyRequest -> IO LazyByteString.ByteString
runParser inputFileName verifyRequest = do
    fileContent <- ByteString.readFile inputFileName
    let
        unverifiedDefinition = fromKore fileContent
        definition =
            case verifyRequest of
                VerifyRequestYes -> verify unverifiedDefinition
                VerifyRequestNo  -> unverifiedDefinition
    return (toByteString definition)

