module Data.Kore.Implicit.ImplicitKoreTest
    ( implicitKoreRegressionTests
    ) where

import           Test.Tasty        (TestTree, testGroup)
import           Test.Tasty.Golden (goldenVsString)

import           Data.Kore.Implicit.Verified     (implicitKoreDefinition)
import           Data.Kore.MetaML.AST
import           Data.Kore.Parser.RegressionTest (GoldenFileName(..),
                                                  InputFileName(..),
                                                  VerifyRequest(..),
                                                  regressionTest)
import           Data.Kore.Unparser.Unparse      (unparseToString)

import qualified Data.ByteString.Lazy       as LazyByteString
import qualified Data.ByteString.Lazy.Char8 as LazyChar8

implicitKoreRegressionTests :: InputFileName -> GoldenFileName -> TestTree
implicitKoreRegressionTests inputFileName goldenFileName =
    testGroup
        "Implicit kore tests"
        [ implicitKoreTest inputFileName
        , regressionTest inputFileName goldenFileName VerifyRequestNo
        ]

implicitKoreTest :: InputFileName -> TestTree
implicitKoreTest (InputFileName inputFileName) =
    goldenVsString
        "Testing the implicit kore"
        inputFileName
        (toByteString implicitKoreDefinition)

toByteString :: MetaDefinition -> IO LazyByteString.ByteString
toByteString m = return (LazyChar8.pack (unparseToString m))
