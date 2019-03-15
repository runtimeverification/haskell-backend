module Test.Kore.Parser.Regression
    ( InputFileName (..)
    , GoldenFileName (..)
    , regressionTest
    , regressionTests
    , regressionTestsInputFiles
    , test_regression
    , VerifyRequest(..)
    ) where

import Test.Tasty
       ( TestTree )
import Test.Tasty.Golden
       ( findByExtension, goldenVsString )

import           Control.Exception
                 ( bracket )
import           Data.ByteString.Lazy
                 ( ByteString )
import qualified Data.ByteString.Lazy.Char8 as ByteString.Lazy.Char8
import           System.Directory
                 ( getCurrentDirectory, setCurrentDirectory )
import           System.FilePath
                 ( addExtension, splitFileName, (</>) )

import           Kore.AST.Sentence
import           Kore.ASTVerifier.DefinitionVerifier
import qualified Kore.Builtin as Builtin
import           Kore.Error
import           Kore.Parser.Parser

import qualified Paths

newtype InputFileName = InputFileName FilePath
newtype GoldenFileName = GoldenFileName FilePath

data VerifyRequest = VerifyRequestYes | VerifyRequestNo

regressionTests :: [InputFileName] -> [TestTree]
regressionTests = map regressionTestFromInputFile

regressionTestsInputFiles :: String -> IO [InputFileName]
regressionTestsInputFiles dir = do
    files <-
        withCurrentDirectory
            (Paths.dataFileName ".") (findByExtension [".kore"] dir)
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

toByteString :: Either String KoreDefinition -> ByteString
toByteString (Left err) = ByteString.Lazy.Char8.pack err
toByteString (Right _) = ByteString.Lazy.Char8.empty

verify :: KoreDefinition -> Either String KoreDefinition
verify definition =
    case
        verifyDefinition
            defaultNullAttributesVerification
            Builtin.koreVerifiers
            definition
      of
        Left e  -> Left (printError e)
        Right _ -> Right definition

runParser :: String -> VerifyRequest -> IO ByteString
runParser inputFileName verifyRequest = do
    input <- readInput
    let
        definition = do
            unverified <- parseKoreDefinition inputFileName input
            case verifyRequest of
                VerifyRequestYes -> verify unverified
                VerifyRequestNo  -> return unverified
    return (toByteString definition)
  where
    readInput =
        withCurrentDirectory
            (Paths.dataFileName ".")
            (readFile inputFileName)

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
    regressionTests <$> regressionTestsInputFiles "../src/test/resources/"
