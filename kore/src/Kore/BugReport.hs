{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.BugReport
    ( unparseKoreLogOptions
    , unparseKoreMergeOptions
    , unparseKoreProveOptions
    , writeKoreMergeFiles
    , writeKoreProveFiles
    ) where

import Prelude.Kore

import qualified Data.Char as Char
import qualified Data.Set as Set
import qualified Data.Foldable as Foldable
import qualified Data.Text as Text
import Data.List
    ( intercalate
    )

import Kore.Log.KoreLogOptions
import Kore.Log.DebugSolver
    ( DebugSolverOptions (..)
    )
import Kore.Syntax.Definition
    ( ModuleName (..)
    )
import Kore.Step.Strategy
    ( GraphSearchOrder (..)
    )
import Kore.Log.SQLite
    ( LogSQLiteOptions (..)
    )
import System.Directory
    ( copyFile
    )
import GlobalMain

unparseKoreLogOptions :: KoreLogOptions -> [String]
unparseKoreLogOptions
    ( KoreLogOptions
        logType
        logLevel
        timestampsSwitch
        logEntries
        debugSolverOptions
        _
        logSQLiteOptions
        warningSwitch
        debugApplyEquationOptions
        debugAttemptEquationOptions
        debugEquationOptions
    )
  =
    concat
        [ koreLogTypeFlag logType
        , ["--log-level", fmap Char.toLower (show logLevel)]
        , timestampsSwitchFlag timestampsSwitch
        , logEntriesFlag logEntries
        , debugSolverOptionsFlag debugSolverOptions
        , logSQLiteOptionsFlag logSQLiteOptions
        , ["--warnings-to-errors" | AsError <- [warningSwitch] ]
        , debugApplyEquationOptionsFlag debugApplyEquationOptions
        , debugAttemptEquationOptionsFlag debugAttemptEquationOptions
        , debugEquationOptionsFlag debugEquationOptions
        ]
  where
    koreLogTypeFlag LogStdErr = []
    koreLogTypeFlag (LogFileText file) = ["--log ", file]

    timestampsSwitchFlag TimestampsEnable = ["--enable-log-timestamps"]
    timestampsSwitchFlag TimestampsDisable = ["--disable-log-timestamps"]

    logEntriesFlag entries
      | Set.null entries = []
      | otherwise
      = [ "--log-entries "
        , intercalate "," (fmap show (Foldable.toList entries))
        ]   

    debugSolverOptionsFlag (DebugSolverOptions Nothing) = []
    debugSolverOptionsFlag (DebugSolverOptions (Just file)) =
        ["--solver-transcript ", file]

    logSQLiteOptionsFlag (LogSQLiteOptions Nothing) = []
    logSQLiteOptionsFlag (LogSQLiteOptions (Just file)) =
        ["--sqlog ", file]

    debugApplyEquationOptionsFlag (DebugApplyEquationOptions set) =
        ("--debug-apply-equation " <>) . Text.unpack <$> Foldable.toList set

    debugAttemptEquationOptionsFlag (DebugAttemptEquationOptions set) =
        ("--debug-attempt-equation " <>) . Text.unpack <$> Foldable.toList set

    debugEquationOptionsFlag (DebugEquationOptions set) =
        ("--debug-equation " <>) . Text.unpack <$> Foldable.toList set

unparseKoreMergeOptions :: KoreMergeOptions -> [String]
unparseKoreMergeOptions (KoreMergeOptions _ maybeBatchSize) =
    [ "--merge-rules mergeRules.kore"]
    <> maybe mempty ((:[]) . ("--merge-batch-size " <>) . show) maybeBatchSize

unparseKoreProveOptions :: KoreProveOptions -> [String]
unparseKoreProveOptions
    ( KoreProveOptions
        _
        (ModuleName moduleName)
        graphSearch
        bmc
        saveProofs
    )
  =
    [ "--prove spec.kore"
    , "--spec-module " <> Text.unpack moduleName
    , "--graph-search "
        <> if graphSearch == DepthFirst then "depth-first" else "breadth-first"
    , if bmc then "--bmc" else ""
    , maybe "" ("--save-proofs " <>) saveProofs
    ]

writeKoreMergeFiles :: FilePath -> KoreMergeOptions -> IO ()
writeKoreMergeFiles reportFile KoreMergeOptions { rulesFileName } =
    copyFile rulesFileName $ reportFile <> "/mergeRules.kore"

writeKoreProveFiles :: FilePath -> KoreProveOptions -> IO ()
writeKoreProveFiles reportFile KoreProveOptions { specFileName, saveProofs } = do
    copyFile specFileName $ reportFile <> "/spec.kore"
    Foldable.forM_ saveProofs $ flip copyFile (reportFile <> "/saveProofs.kore")