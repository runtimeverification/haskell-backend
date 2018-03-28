import           Test.Tasty                               (TestTree, testGroup)

import           Test.Tasty.Runners                       (consoleTestReporter, defaultMainWithIngredients,
                                                           listingTests)
import           Test.Tasty.Runners.AntXML                (antXMLRunner)

import           Data.Kore.ASTHelpersTest
import           Data.Kore.ASTTraversalsTest
import           Data.Kore.ASTVerifier.ASTVerifierTest
import           Data.Kore.Implicit.ImplicitKoreTest
import           Data.Kore.IndentingPrinterTest
import           Data.Kore.MetaML.LiftUnliftTest
import           Data.Kore.MetaML.UnliftTest
import           Data.Kore.Parser.CharDictTest
import           Data.Kore.Parser.CharSetTest
import           Data.Kore.Parser.CStringTest
import           Data.Kore.Parser.LexemeTest
import           Data.Kore.Parser.ParserTest
import           Data.Kore.Parser.RegressionTest
import           Data.Kore.Substitution.ClassTest
import           Data.Kore.Substitution.ListTest
import           Data.Kore.Unparser.UnparseTest
import           Data.Kore.Variables.Fresh.IntCounterTest
import           Data.Kore.Variables.IntTest

main :: IO ()
main = do
    inputFiles <- regressionTestsInputFiles "../../../test/resources/"
    defaultMainWithIngredients
        [antXMLRunner, listingTests, consoleTestReporter]
        (allParserTests inputFiles)

allParserTests :: [InputFileName] -> TestTree
allParserTests regressionInputFiles =
    testGroup
        " All Parser Tests"
        [ unitTests
        , regressionTests regressionInputFiles
        , implicitKoreRegressionTests
            (InputFileName "../../kore/kore.kore")
            (GoldenFileName "../../../test/expected/kore.kore.golden")
        ]

unitTests :: TestTree
unitTests =
    testGroup
        " Unit Tests"
        [ astVerifierTests
        , astHelperTests
        , charDictTests
        , charSetTests
        , cStringTests
        , koreLexemeTests
        , koreParserTests
        , indentingPrinterTests
        , unparseUnitTests
        , unparseParseTests
        , astTraversalsTests
        , variablesFreshIntCounterTests
        , variablesIntTests
        , substitutionListTests
        , substitutionClassTests
        , liftTests
        , unliftTests
        ]
