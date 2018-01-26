import           Test.Tasty

import           Data.Kore.Parser.CharDictTest
import           Data.Kore.Parser.CharSetTest
import           Data.Kore.Parser.CStringTest
import           Data.Kore.Parser.LexemeTest
import           Data.Kore.Parser.ParserTest
import           Data.Kore.Parser.RegressionTest
import           Data.Kore.Unparser.UnparseTest

main :: IO ()
main = do
    inputFiles <- regressionTestsInputFiles "../../../test/resources/"
    defaultMain (allParserTests inputFiles)

allParserTests :: [String] -> TestTree
allParserTests regressionInputFiles =
    testGroup
        " All Parser Tests"
        [ unitTests
        , regressionTests regressionInputFiles
        ]

unitTests :: TestTree
unitTests =
    testGroup
        " Unit Tests"
        [ charDictTests
        , charSetTests
        , cStringTests
        , koreLexemeTests
        , koreParserTests
        , unparseParseTests
        ]
