module Test.Kore.BugReport (
    test_Parse_BugReportOption,
    test_parse,
) where

import Data.List qualified as List
import Debug
import Hedgehog
import Hedgehog.Gen qualified as Gen
import Hedgehog.Range qualified as Range
import Kore.BugReport (
    BugReport (..),
    BugReportOption (..),
    parseBugReportOption,
 )
import Kore.Log (
    parseKoreLogOptions,
    unparseKoreLogOptions,
 )
import Kore.Log.KoreLogOptions (
    ExeName (..),
    KoreLogOptions,
 )
import Kore.Log.Registry (
    entryTypeReps,
 )
import Options.Applicative
import Prelude.Kore
import Pretty qualified
import System.Clock (
    fromNanoSecs,
 )
import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Hedgehog

test_parse :: TestTree
test_parse =
    testGroup
        "Parse KoreLogOptions"
        [ testProperty "Parse KoreLogOptions" myProperty
        ]
  where
    myProperty = property $ do
        logType <- forAll $ element [[], ["--log", "logFile.log"]]
        logLevel <-
            forAllFlags
                [ ["--log-level", level]
                | level <- ["debug", "info", "warning", "error"]
                ]
        timestampsSwitch <-
            forAllFlags
                [["--enable-log-timestamps"], ["--disable-log-timestamps"]]
        logEntries <- forAll $ do
            shuffled <- Gen.shuffle (fmap show entryTypeReps)
            subseq <- Gen.subsequence shuffled
            let values = [List.intercalate "," subseq]
            return $ "--log-entries" : values
        debugSolverOptions <-
            forAllFlags
                [["--solver-transcript", "transcriptFile"]]
        logSQLiteOptions <- forAllFlags [["--sqlog", "sqlogFile"]]
        warningSwitch <- forAllFlags [["--warnings-to-errors"]]
        optionsNumber <- forAll $ Gen.integral (Range.linear 0 (3 :: Int))
        let debugApplyEquationOptions =
                concat
                    [ ["--debug-apply-equation", "eq" <> show index]
                    | index <- [0 .. optionsNumber]
                    ]
            debugAttemptEquationOptions =
                concat
                    [ ["--debug-attempt-equation", "eq" <> show index]
                    | index <- [0 .. optionsNumber]
                    ]
            debugEquationOptions =
                concat
                    [ ["--debug-equation", "eq" <> show index]
                    | index <- [0 .. optionsNumber]
                    ]

        let arguments =
                concat
                    [ logType
                    , logLevel
                    , timestampsSwitch
                    , logEntries
                    , debugSolverOptions
                    , logSQLiteOptions
                    , warningSwitch
                    , debugApplyEquationOptions
                    , debugAttemptEquationOptions
                    , debugEquationOptions
                    ]
        let expect :: ParserResult KoreLogOptions
            expect = parseKoreLogOpts arguments
        let actual :: ParserResult KoreLogOptions
            actual = expect >>= parseKoreLogOpts . unparseKoreLogOptions
        getParseResult expect === getParseResult actual

test_Parse_BugReportOption :: [TestTree]
test_Parse_BugReportOption =
    [ testParse
        "Parse BugReportEnable"
        ["--bug-report", "fileName"]
        (BugReportEnable $ BugReport "fileName")
    , testParse
        "Parse BugReportDisable"
        ["--no-bug-report"]
        BugReportDisable
    , testParse "Parse BugReportOnError" [] BugReportOnError
    ]
  where
    testParse :: TestName -> [String] -> BugReportOption -> TestTree
    testParse testName arguments opt =
        testCase testName $ assertParse arguments opt

    assertParse :: HasCallStack => [String] -> BugReportOption -> Assertion
    assertParse arguments opt =
        assertEqual
            ( show $
                Pretty.vsep
                    [ "while parsing:"
                    , Pretty.indent 4 (debug arguments)
                    , "expected:"
                    , Pretty.indent 4 (debug opt)
                    ]
            )
            (Just opt)
            (getParseResult $ parseBugReportOpts arguments)

parseKoreLogOpts :: [String] -> ParserResult KoreLogOptions
parseKoreLogOpts arguments =
    execParserPure
        defaultPrefs
        ( info
            (parseKoreLogOptions (ExeName "kore-exec") (fromNanoSecs 0))
            fullDesc
        )
        arguments

parseBugReportOpts :: [String] -> ParserResult BugReportOption
parseBugReportOpts arguments =
    execParserPure
        defaultPrefs
        (info parseBugReportOption fullDesc)
        arguments

element :: [a] -> Gen a
element list = do
    index <- Gen.integral (Range.linear 0 (length list - 1))
    pure $ list !! index

forAllFlags :: [[String]] -> PropertyT IO [String]
forAllFlags = forAll . element . ([] :)
