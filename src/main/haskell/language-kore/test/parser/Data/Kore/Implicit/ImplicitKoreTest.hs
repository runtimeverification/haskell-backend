module Data.Kore.Implicit.ImplicitKoreTest (implicitKoreRegressionTests) where

import           Test.Tasty                      (TestTree, testGroup)
import           Test.Tasty.Golden               (goldenVsString)

import           Data.Kore.AST.Kore
import           Data.Kore.AST.Sentence
import           Data.Kore.Parser.RegressionTest (GoldenFileName (..),
                                                  InputFileName (..),
                                                  VerifyRequest (..),
                                                  regressionTest)
import           Data.Kore.Unparser.Unparse      (unparseToString)

import qualified Data.ByteString.Lazy            as LazyByteString
import qualified Data.ByteString.Lazy.Char8      as LazyChar8

implicitKoreRegressionTests
    :: KoreDefinition -> InputFileName -> GoldenFileName -> TestTree
implicitKoreRegressionTests definition inputFileName goldenFileName =
    testGroup "Implicit kore tests"
        [ implicitKoreTest definition inputFileName
        , regressionTest inputFileName goldenFileName VerifyRequestNo
        ]

implicitKoreTest :: KoreDefinition -> InputFileName -> TestTree
implicitKoreTest definition (InputFileName inputFileName) =
    goldenVsString
        "Testing the implicit kore"
        inputFileName
        (toByteString definition)

toByteString :: KoreDefinition -> IO LazyByteString.ByteString
toByteString m =
    return (LazyChar8.pack (unparseToString m))
