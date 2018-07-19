module Test.Data.Kore.Implicit.ImplicitKore (test_implicitKore, test_implicitAttributes) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.Golden
       ( goldenVsString )

import Data.Kore.AST.Sentence
import Data.Kore.Implicit.Verified
       ( implicitAttributesDefinition, implicitKoreDefinition )
import Data.Kore.Unparser.Unparse
       ( unparseToString )
import Test.Data.Kore.Parser.Regression
       ( GoldenFileName (..), InputFileName (..), VerifyRequest (..),
       regressionTest )

import qualified Data.ByteString.Lazy as LazyByteString
import qualified Data.ByteString.Lazy.Char8 as LazyChar8

import qualified Paths

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
        (Paths.dataFileName inputFileName)
        (toByteString definition)

toByteString :: KoreDefinition -> IO LazyByteString.ByteString
toByteString m =
    return (LazyChar8.pack (unparseToString m))

test_implicitKore :: TestTree
test_implicitKore =
    implicitKoreRegressionTests
        implicitKoreDefinition
        (InputFileName "../../kore/kore.kore")
        (GoldenFileName "../../../test/expected/kore.kore.golden")

test_implicitAttributes :: TestTree
test_implicitAttributes =
    implicitKoreRegressionTests
        implicitAttributesDefinition
        (InputFileName "../../kore/attributes.kore")
        (GoldenFileName "../../../test/expected/attributes.kore.golden")
