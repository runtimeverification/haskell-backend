module Test.Data.Kore.Parser.Regression
    ( InputFileName (..)
    , GoldenFileName (..)
    , VerifyRequest(..)
    , regressionTest, test_regression
    ) where

import           Test.Tasty                               (TestTree)
import           Test.Tasty.Golden                        (findByExtension,
                                                           goldenVsString)

import           Data.Kore.AST.Sentence
import           Data.Kore.ASTPrettyPrint
import           Data.Kore.ASTVerifier.DefinitionVerifier
import           Data.Kore.Error
import           Data.Kore.Parser.Parser


import Control.Exception (bracket)
import qualified Data.ByteString.Lazy                     as LazyByteString
import qualified Data.ByteString.Lazy.Char8               as LazyChar8
import System.Directory (getCurrentDirectory, setCurrentDirectory)
import           System.FilePath                          (addExtension,
                                                           splitFileName, (</>))

import qualified Paths

newtype InputFileName = InputFileName FilePath
newtype GoldenFileName = GoldenFileName FilePath

data VerifyRequest = VerifyRequestYes | VerifyRequestNo

regressionTests :: [InputFileName] -> [TestTree]
regressionTests = map regressionTestFromInputFile

regressionTestsInputFiles :: String -> IO [InputFileName]
regressionTestsInputFiles dir = do
    files <- withCurrentDirectory (Paths.dataFileName ".") (findByExtension [".kore"] dir)
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
        (Paths.dataFileName goldenFileName)
        (runParser inputFileName verifyRequest)

goldenFromInputFileName :: InputFileName -> GoldenFileName
goldenFromInputFileName (InputFileName inputFile) =
    GoldenFileName
        (directory </> "expected" </> addExtension inputFileName ".golden")
  where (directory, inputFileName) = splitFileName inputFile

toByteString :: Either String KoreDefinition -> LazyByteString.ByteString
toByteString (Left err) =
    LazyChar8.pack ("Parse error: " ++ err)
toByteString (Right definition) =
    LazyChar8.pack (prettyPrintToString definition)

verify :: Either String KoreDefinition -> Either String KoreDefinition
verify (Left err) = Left err
verify (Right definition) =
    case verifyDefinition attributesVerification definition of
        Left e  -> Left (printError e)
        Right _ -> Right definition
  where
    attributesVerification :: AttributesVerification
    attributesVerification = case defaultAttributesVerification of
        Right verification -> verification
        Left err           -> error (printError err)


runParser :: String -> VerifyRequest -> IO LazyByteString.ByteString
runParser inputFileName verifyRequest = do
    fileContent <- withCurrentDirectory (Paths.dataFileName ".") (readFile inputFileName)
    let
        unverifiedDefinition = fromKore inputFileName fileContent
        definition =
            case verifyRequest of
                VerifyRequestYes -> verify unverifiedDefinition
                VerifyRequestNo  -> unverifiedDefinition
    return (toByteString definition)

withCurrentDirectory :: FilePath -> IO a -> IO a
withCurrentDirectory dir go =
    bracket pushd popd (const go)
  where
    pushd =
        do cur <- getCurrentDirectory
           setCurrentDirectory dir
           pure cur
    popd = setCurrentDirectory

test_regression :: IO [TestTree]
test_regression =
    regressionTests <$> regressionTestsInputFiles "../../../test/resources/"
