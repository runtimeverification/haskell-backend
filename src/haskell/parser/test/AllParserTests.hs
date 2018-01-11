import           Test.Tasty

import           KoreParserTest
import           KoreLexemeTest

main :: IO ()
main = defaultMain allParserTests

allParserTests :: TestTree
allParserTests =
    testGroup
        " All Parser Tests"
        [koreParserTests, koreLexemeTests]
