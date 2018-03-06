import           Test.Tasty                (TestTree, testGroup)
import           Test.Tasty.Runners        (consoleTestReporter,
                                            defaultMainWithIngredients,
                                            listingTests)
import           Test.Tasty.Runners.AntXML (antXMLRunner)

main :: IO ()
main =
    defaultMainWithIngredients
        [antXMLRunner, listingTests, consoleTestReporter]
        allParserTests

allParserTests :: TestTree
allParserTests =
    testGroup
        " All Matching Logic Tests"
        [ unitTests
        ]

unitTests :: TestTree
unitTests =
    testGroup
        " Unit Tests"
        [
        ]
