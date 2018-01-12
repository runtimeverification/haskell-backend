import           Test.Tasty

import           CharDictTest
import           CStringTest
import           KoreParserTest
import           KoreLexemeTest

main :: IO ()
main = defaultMain allParserTests

allParserTests :: TestTree
allParserTests =
    testGroup
        " All Parser Tests"
        [koreParserTests, koreLexemeTests, cStringTests, charDictTests]
