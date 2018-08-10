module Test.Kore.Implicit.ImplicitKore
    ( test_implicitKore
    ) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.Golden
       ( goldenVsString )

import qualified Data.ByteString.Lazy as LazyByteString
import qualified Data.ByteString.Lazy.Char8 as LazyChar8

import Kore.AST.Sentence
import Kore.Implicit.Verified
       ( implicitKoreDefinition )
import Kore.Unparser.Unparse
       ( unparseToString )

import qualified Paths
import           Test.Kore.Parser.Regression
                 ( GoldenFileName (..), InputFileName (..), VerifyRequest (..),
                 regressionTest )

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
