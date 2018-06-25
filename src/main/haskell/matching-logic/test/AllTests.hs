import           Test.Tasty                                        (TestTree,
                                                                    testGroup)
import           Test.Tasty.Runners                                (consoleTestReporter,
                                                                    defaultMainWithIngredients,
                                                                    listingTests)
import           Test.Tasty.Runners.AntXML                         (antXMLRunner)

import           Kore.MatchingLogic.ProofSystem.ProofAssistantTest
import           Kore.MatchingLogic.ProofSystem.OnePlusOne
import           RuleParserTests

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
        [ proofAssistantTests
        , testMinimalOnePlusOne
        , parserUnitTests
        ]


parserUnitTests :: TestTree
parserUnitTests = testGroup
                    " Rule Parser/Unparser Unit Tests"
                    [  ruleParsingTests
                      ,ruleUnparsingTests
                    ]
