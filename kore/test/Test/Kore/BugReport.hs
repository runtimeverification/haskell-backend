module Test.Kore.BugReport
    ( test_bugReportOption
    , test_parse
    ) where

import Prelude.Kore

import qualified Data.List as List

import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range

import Kore.BugReport
    ( BugReport (..)
    , BugReportOption (..)
    , parseBugReportOption
    )

import Kore.Log
    ( parseKoreLogOptions
    , unparseKoreLogOptions
    )
import Kore.Log.KoreLogOptions
    ( ExeName (..)
    , KoreLogOptions
    )
import Kore.Log.Registry
    ( entryTypeReps
    )
import System.Clock
    ( fromNanoSecs
    )

import Options.Applicative

import Test.Tasty
import Test.Tasty.Hedgehog
import Test.Tasty.HUnit

test_parse :: TestTree
test_parse =
    testGroup
        "Parse KoreLogOptions"
        [ testProperty "Parse KoreLogOptions" myProperty
        ]
  where
    myProperty = property $ do
        logType <- forAll $ element [[], ["--log", "logFile.log"]]
        logLevel <- forAllFlags
                [ ["--log-level", level]
                    | level <- ["debug", "info", "warning", "error"]
                ]
        timestampsSwitch <- forAllFlags
            [["--enable-log-timestamps"], ["--disable-log-timestamps"]]
        logEntries <- forAll $ do
            shuffled <- Gen.shuffle (fmap show entryTypeReps)
            subseq <- Gen.subsequence shuffled
            let values = [List.intercalate "," subseq]
            return $ "--log-entries" : values
        debugSolverOptions <- forAllFlags
            [["--solver-transcript", "transcriptFile"]]
        logSQLiteOptions <- forAllFlags [["--sqlog", "sqlogFile"]]
        warningSwitch <- forAllFlags [["--warnings-to-errors"]]
        optionsNumber <- forAll $ Gen.integral (Range.linear 0 (3 :: Int))
        let debugApplyEquationOptions = concat
                [ ["--debug-apply-equation", "eq" <> show index]
                    | index <- [0..optionsNumber]
                ]
            debugAttemptEquationOptions = concat
                [ ["--debug-attempt-equation", "eq" <> show index]
                    | index <- [0..optionsNumber]
                ]
            debugEquationOptions = concat
                [ ["--debug-equation", "eq" <> show index]
                    | index <- [0..optionsNumber]
                ]

        let arguments = concat
                [ logType, logLevel, timestampsSwitch, logEntries
                , debugSolverOptions, logSQLiteOptions, warningSwitch
                , debugApplyEquationOptions, debugAttemptEquationOptions
                , debugEquationOptions
                ]
        let
            expect :: ParserResult KoreLogOptions
            expect = parseKoreLogOpts arguments
        let
            actual :: ParserResult KoreLogOptions
            actual = expect >>= parseKoreLogOpts . unparseKoreLogOptions
        getParseResult expect === getParseResult actual

test_bugReportOption :: TestTree
test_bugReportOption =
    testGroup
        "Parse BugReportOption"
        [ testCase "Parse BugReportEnable" enableAssert
        , testCase "Parse BugReportDisable" disableAssert
        , testCase "Parse BugReportOnError" onErrorAssert
        ]
  where
    enableAssert =
        assertParse
            ["--bug-report", "fileName"]
            (BugReportEnable $ BugReport "fileName")

    disableAssert =
        assertParse
            ["--no-bug-report"]
            BugReportDisable

    onErrorAssert =
        assertParse
            []
            BugReportOnError

    assertParse :: [String] -> BugReportOption -> Assertion
    assertParse arguments opt =
        assertEqual
            (show $ Pretty.vsep
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
forAllFlags = forAll . element . ([]:)
