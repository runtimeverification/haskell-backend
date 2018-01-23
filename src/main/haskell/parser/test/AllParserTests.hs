import           Test.Tasty

import           CharDictTest
import           CharSetTest
import           CStringTest
import           LexemeTest
import           ParserTest
import           RegressionTest

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
        ]
