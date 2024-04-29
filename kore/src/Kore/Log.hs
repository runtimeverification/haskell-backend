{-# LANGUAGE RecordWildCards #-}

{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Log (
    koreLogFilters,
    koreLogTransformer,
    withLoggerLegacy,
    emptyLogger,
    stderrLogger,
    swappableLogger,
    makeKoreLoggerLegacy,
    Colog.logTextStderr,
    Colog.logTextHandle,
    runKoreLog,
    runKoreLogThreadSafe,
    runKoreLogThreadSafeLegacy,
    WithTimestamp (..),
    withTimestamp,
    withSmtSolverLogger,
    module Log,
    module KoreLogOptions,
) where

import Colog (
    LogAction (..),
 )
import Colog qualified
import Control.Concurrent.MVar
import Control.Monad.Catch (
    MonadMask,
 )
import Control.Monad.Catch qualified as Exception
import Control.Monad.Cont (
    ContT (..),
    runContT,
 )
import Data.Functor.Contravariant (
    contramap,
 )
import Data.Text (
    Text,
 )
import Kore.Log.DebugRewriteTrace (
    rewriteTraceLogger,
 )
import Kore.Log.DebugSolver (
    DebugSolverOptions (DebugSolverOptions),
    solverTranscriptLogger,
 )
import Kore.Log.DebugSolver qualified as DebugSolver.DoNotUse
import Kore.Log.KoreLogOptions as KoreLogOptions
import Kore.Log.Registry (
    lookupTextFromTypeWithError,
    typeOfSomeEntry,
 )
import Kore.Log.SQLite
import Log
import Prelude.Kore
import Pretty qualified
import System.Clock (
    Clock (Monotonic),
    TimeSpec (..),
    diffTimeSpec,
    getTime,
    toNanoSecs,
 )
import System.Directory (
    doesDirectoryExist,
    doesFileExist,
 )
import System.FilePath (
    takeDirectory,
    (<.>),
    (</>),
 )
import System.IO (
    hPutStrLn,
    stderr,
 )

-- | Internal type used to add timestamps to a 'LogMessage'.
data WithTimestamp = WithTimestamp SomeEntry TimeSpec

{- | Generates an appropriate logger for the given 'KoreLogOptions'. It uses
 the CPS style because some outputters require cleanup (e.g. files).
-}
withLoggerLegacy ::
    FilePath ->
    KoreLogOptions ->
    (LogAction IO SomeEntry -> IO a) ->
    IO a
withLoggerLegacy reportDirectory koreLogOptions = runContT $ do
    mainLogger <- ContT $ withMainLoggerLegacy reportDirectory koreLogOptions
    let KoreLogOptions{exeName, debugSolverOptions} = koreLogOptions
    smtSolverLogger <- ContT $ withSmtSolverLogger exeName debugSolverOptions
    traceLogger <- ContT $ withRewriteTraceLogger koreLogOptions
    let KoreLogOptions{logSQLiteOptions} = koreLogOptions
    logSQLite <- ContT $ withLogSQLite logSQLiteOptions
    return $ mainLogger <> smtSolverLogger <> traceLogger <> logSQLite

withMainLoggerLegacy ::
    FilePath ->
    KoreLogOptions ->
    (LogAction IO SomeEntry -> IO a) ->
    IO a
withMainLoggerLegacy reportDirectory koreLogOptions = runContT $ do
    let KoreLogOptions{exeName, startTime} = koreLogOptions
        bugReportLogFile = reportDirectory </> getExeName exeName <.> "log"
    bugReportLogAction <- ContT $ Colog.withLogTextFile bugReportLogFile
    userLogAction <-
        case logType koreLogOptions of
            LogBooster _ -> pure Colog.logTextStderr
            LogStdErr -> pure Colog.logTextStderr
            LogFileText logFile -> do
                lift (checkLogFilePath exeName "" logFile) >>= ContT . Colog.withLogTextFile
    let KoreLogOptions{timestampsSwitch} = koreLogOptions
        KoreLogOptions{logFormat} = koreLogOptions
        logAction =
            userLogAction <> bugReportLogAction
                & makeKoreLoggerLegacy exeName startTime timestampsSwitch logFormat
                & koreLogFilters koreLogOptions
                & koreLogTransformer koreLogOptions
    pure logAction

{- | Checks if the user supplied path for logging exists. If it doesn't, or if the file
    already exists, will return a default logging location at ./[exe-name]-[prefix]-[timestamp].log
-}
checkLogFilePath :: ExeName -> String -> FilePath -> IO FilePath
checkLogFilePath exeName prefix logFile = do
    pathExists <- doesDirectoryExist $ takeDirectory logFile
    fileExists <- doesFileExist logFile
    currentTime <- (`div` 1000) . toNanoSecs <$> getTime Monotonic
    let defaultLogFile = "." </> (getExeName exeName <> "-" <> prefix <> "-" <> show currentTime) <.> "log"
    if not pathExists
        then do
            hPutStrLn stderr $
                getExeName exeName
                    <> ": Warning: the path '"
                    <> takeDirectory logFile
                    <> "' does not exist. Logging to '"
                    <> defaultLogFile
                    <> "' instead."
            pure defaultLogFile
        else
            if fileExists
                then do
                    hPutStrLn stderr $
                        getExeName exeName
                            <> ": Warning: the file '"
                            <> logFile
                            <> "' already exists. Logging to '"
                            <> defaultLogFile
                            <> "' instead."
                    pure defaultLogFile
                else pure logFile

withSmtSolverLogger ::
    ExeName -> DebugSolverOptions -> (LogAction IO SomeEntry -> IO a) -> IO a
withSmtSolverLogger exeName DebugSolverOptions{logFile} continue =
    case logFile of
        Nothing -> continue mempty
        Just filename' -> do
            filename <- checkLogFilePath exeName "smt" filename'
            writeFile filename ""
            Colog.withLogTextFile
                filename
                (continue . solverTranscriptLogger)

withRewriteTraceLogger ::
    KoreLogOptions -> (LogAction IO SomeEntry -> IO a) -> IO a
withRewriteTraceLogger KoreLogOptions{rewriteTraceFileName} continue =
    case rewriteTraceFileName of
        Nothing -> continue mempty
        Just filename -> do
            writeFile filename ""
            Colog.withLogByteStringFile
                filename
                (continue . rewriteTraceLogger)

koreLogTransformer ::
    KoreLogOptions ->
    LogAction m SomeEntry ->
    LogAction m SomeEntry
koreLogTransformer koreLogOptions baseLogger =
    Colog.cmap
        (toErrors warningSwitch)
        baseLogger
  where
    KoreLogOptions{turnedIntoErrors, warningSwitch} = koreLogOptions

    toErrors :: WarningSwitch -> SomeEntry -> SomeEntry
    toErrors AsError entry
        | entrySeverity entry == Warning =
            error . show . longDoc $ entry
    toErrors _ entry
        | typeOfSomeEntry entry `elem` turnedIntoErrors =
            error . show . longDoc $ entry
        | otherwise = entry

koreLogFilters ::
    Applicative m =>
    KoreLogOptions ->
    LogAction m SomeEntry ->
    LogAction m SomeEntry
koreLogFilters koreLogOptions baseLogger =
    let KoreLogOptions{..} = koreLogOptions
     in Colog.cfilter
            ( \entry ->
                filterEntry logEntries entry
                    || filterSeverity logLevel entry
                    || selectDebugApplyEquation debugApplyEquationOptions entry
                    || selectDebugAttemptEquation debugAttemptEquationOptions entry
                    || selectDebugEquation debugEquationOptions entry
                    || selectDebugAttemptRewrite debugAttemptRewriteOptions entry
                    || selectDebugApplyRewrite debugApplyRewriteOptions entry
                    || selectDebugRewrite debugRewriteOptions entry
            )
            baseLogger

-- | Select the log entry types present in the active set.
filterEntry ::
    EntryTypes ->
    SomeEntry ->
    Bool
filterEntry logEntries entry =
    typeOfSomeEntry entry `elem` logEntries

-- | Select log entries with 'Severity' greater than or equal to the level.
filterSeverity ::
    Severity ->
    SomeEntry ->
    Bool
filterSeverity level entry =
    entrySeverity entry >= level

-- | Run a 'LoggerT' with the given options.
runKoreLog :: FilePath -> KoreLogOptions -> LoggerT IO a -> IO a
runKoreLog reportDirectory options loggerT =
    withLoggerLegacy reportDirectory options $ runLoggerT loggerT

-- | Run a 'LoggerT' with the given options, using `swappableLogger` to make it thread safe.
runKoreLogThreadSafeLegacy :: FilePath -> KoreLogOptions -> LoggerT IO a -> IO a
runKoreLogThreadSafeLegacy reportDirectory options loggerT =
    withLoggerLegacy reportDirectory options $ \actualLogAction -> do
        mvarLogAction <- newMVar actualLogAction
        let swapLogAction = swappableLogger mvarLogAction
        runLoggerT loggerT swapLogAction

-- | Run a 'LoggerT' with the given options, using `swappableLogger` to make it thread safe.
runKoreLogThreadSafe :: KoreLogOptions -> LoggerT IO a -> IO a
runKoreLogThreadSafe options loggerT =
    withLogger options $ \actualLogAction -> do
        mvarLogAction <- newMVar actualLogAction
        let swapLogAction = swappableLogger mvarLogAction
        runLoggerT loggerT swapLogAction

{- | The default Kore logger used by the legacy backend.

Creates a kore logger which:
  * adds timestamps
  * formats messages: "<exe-name>: [<timestamp>] <severity> (<entry-type>): <message>"
-}
makeKoreLoggerLegacy ::
    forall io.
    MonadIO io =>
    ExeName ->
    TimeSpec ->
    TimestampsSwitch ->
    KoreLogFormat ->
    LogAction io Text ->
    LogAction io SomeEntry
makeKoreLoggerLegacy exeName startTime timestampSwitch _koreLogFormat logActionText =
    logActionText
        & contramap (renderStandardPretty exeName startTime timestampSwitch)
        & Colog.cmapM withTimestamp

renderStandardPretty :: ExeName -> TimeSpec -> TimestampsSwitch -> WithTimestamp -> Text
renderStandardPretty exeName startTime timestampSwitch (WithTimestamp entry@(SomeEntry entryContext actualEntry) entryTime) =
    prettyActualEntry
        & Pretty.layoutPretty Pretty.defaultLayoutOptions
        & Pretty.renderText
  where
    timestamp =
        case timestampSwitch of
            TimestampsDisable -> Nothing
            TimestampsEnable ->
                Just . Pretty.brackets . Pretty.pretty $
                    toMicroSecs (diffTimeSpec startTime entryTime)
    toMicroSecs = (`div` 1000) . toNanoSecs
    exeName' = Pretty.pretty exeName <> Pretty.colon
    prettyActualEntry =
        Pretty.vsep . concat $
            [ [header]
            , indent <$> [longDoc actualEntry]
            , context'
            ]
      where
        shortHeader = "[kore]"

        header =
            (Pretty.hsep . catMaybes)
                [ Just exeName'
                , timestamp
                , Just severity'
                , Just (Pretty.parens $ type' entry)
                ]
                <> Pretty.colon
        severity' = prettySeverity (entrySeverity actualEntry)
        type' e =
            Pretty.pretty $
                lookupTextFromTypeWithError $
                    typeOfSomeEntry e
        context' =
            (entry : entryContext)
                & reverse
                & mapMaybe (\e -> (,type' e) <$> contextDoc e)
                & prettyContext
        prettyContext =
            \case
                [] -> []
                xs -> ("Context" <> Pretty.colon) : (indent <$> mkContext xs)

        oneLineContext =
            entryContext
                & reverse
                & concatMap (\(SomeEntry _ e) -> oneLineContextDoc e)

        mkContext =
            \case
                [] -> []
                [(doc, typeName)] ->
                    [Pretty.hsep [Pretty.parens typeName, doc]]
                (doc, typeName) : xs -> (Pretty.hsep [Pretty.parens typeName, doc]) : (indent <$> (mkContext xs))

    indent = Pretty.indent 4

-- | Adds the current timestamp to a log entry.
withTimestamp :: MonadIO io => SomeEntry -> io WithTimestamp
withTimestamp msg = liftIO $ do
    currentTime <- getTime Monotonic
    pure $ WithTimestamp msg currentTime

emptyLogger :: Applicative m => LogAction m msg
emptyLogger = mempty

stderrLogger ::
    MonadIO io =>
    ExeName ->
    TimeSpec ->
    TimestampsSwitch ->
    KoreLogFormat ->
    LogAction io SomeEntry
stderrLogger exeName startTime timestampsSwitch logFormat =
    makeKoreLoggerLegacy exeName startTime timestampsSwitch logFormat Colog.logTextStderr

{- | @swappableLogger@ delegates to the logger contained in the 'MVar'.

This allows the logger to be "swapped" during execution. (It also automatically
makes the logger thread-safe.)
-}
swappableLogger ::
    (MonadIO m, MonadMask m) =>
    MVar (LogAction m a) ->
    LogAction m a
swappableLogger mvar =
    Colog.LogAction $ Exception.bracket acquire release . worker
  where
    acquire = liftIO $ takeMVar mvar
    release = liftIO . putMVar mvar
    worker a logAction = Colog.unLogAction logAction a
