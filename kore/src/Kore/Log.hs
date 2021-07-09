{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
-}
module Kore.Log (
    koreLogFilters,
    koreLogTransformer,
    withLogger,
    emptyLogger,
    stderrLogger,
    swappableLogger,
    makeKoreLogger,
    Colog.logTextStderr,
    Colog.logTextHandle,
    runKoreLog,
    module Log,
    module KoreLogOptions,
) where

import Colog (
    LogAction (..),
 )
import qualified Colog
import Control.Concurrent.MVar
import Control.Monad.Catch (
    MonadMask,
 )
import qualified Control.Monad.Catch as Exception
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
import Kore.Log.DebugSolver (
    DebugSolverOptions (DebugSolverOptions),
    solverTranscriptLogger,
 )
import qualified Kore.Log.DebugSolver as DebugSolver.DoNotUse
import Kore.Log.KoreLogOptions as KoreLogOptions
import Kore.Log.Registry (
    lookupTextFromTypeWithError,
    typeOfSomeEntry,
 )
import Kore.Log.SQLite
import Log
import Prelude.Kore
import qualified Pretty
import System.Clock (
    Clock (Monotonic),
    TimeSpec,
    diffTimeSpec,
    getTime,
    toNanoSecs,
 )
import System.FilePath (
    (<.>),
    (</>),
 )

-- | Internal type used to add timestamps to a 'LogMessage'.
data WithTimestamp = WithTimestamp ActualEntry TimeSpec

{- | Generates an appropriate logger for the given 'KoreLogOptions'. It uses
 the CPS style because some outputters require cleanup (e.g. files).
-}
withLogger ::
    FilePath ->
    KoreLogOptions ->
    (LogAction IO ActualEntry -> IO a) ->
    IO a
withLogger reportDirectory koreLogOptions = runContT $ do
    mainLogger <- ContT $ withMainLogger reportDirectory koreLogOptions
    let KoreLogOptions{debugSolverOptions} = koreLogOptions
    smtSolverLogger <- ContT $ withSmtSolverLogger debugSolverOptions
    let KoreLogOptions{logSQLiteOptions} = koreLogOptions
    logSQLite <- ContT $ withLogSQLite logSQLiteOptions
    return $ mainLogger <> smtSolverLogger <> logSQLite

withMainLogger ::
    FilePath ->
    KoreLogOptions ->
    (LogAction IO ActualEntry -> IO a) ->
    IO a
withMainLogger reportDirectory koreLogOptions = runContT $ do
    let KoreLogOptions{exeName, startTime} = koreLogOptions
        bugReportLogFile = reportDirectory </> getExeName exeName <.> "log"
    bugReportLogAction <- ContT $ Colog.withLogTextFile bugReportLogFile
    userLogAction <-
        case logType koreLogOptions of
            LogStdErr -> pure Colog.logTextStderr
            LogFileText logFile -> ContT $ Colog.withLogTextFile logFile
    let KoreLogOptions{timestampsSwitch} = koreLogOptions
        KoreLogOptions{logFormat} = koreLogOptions
        logAction =
            userLogAction <> bugReportLogAction
                & makeKoreLogger exeName startTime timestampsSwitch logFormat
                & koreLogFilters koreLogOptions
                & koreLogTransformer koreLogOptions
    pure logAction

withSmtSolverLogger ::
    DebugSolverOptions -> (LogAction IO ActualEntry -> IO a) -> IO a
withSmtSolverLogger DebugSolverOptions{logFile} continue =
    case logFile of
        Nothing -> continue mempty
        Just filename -> do
            writeFile filename ""
            Colog.withLogTextFile
                filename
                (continue . solverTranscriptLogger)

koreLogTransformer ::
    KoreLogOptions ->
    LogAction m ActualEntry ->
    LogAction m ActualEntry
koreLogTransformer koreLogOptions baseLogger =
    Colog.cmap
        (toErrors warningSwitch)
        baseLogger
  where
    KoreLogOptions{turnedIntoErrors, warningSwitch} = koreLogOptions

    toErrors :: WarningSwitch -> ActualEntry -> ActualEntry
    toErrors AsError ActualEntry{actualEntry}
        | entrySeverity actualEntry == Warning =
            error . show . longDoc $ actualEntry
    toErrors _ entry@ActualEntry{actualEntry}
        | typeOfSomeEntry actualEntry `elem` turnedIntoErrors =
            error . show . longDoc $ actualEntry
        | otherwise = entry

koreLogFilters ::
    Applicative m =>
    KoreLogOptions ->
    LogAction m ActualEntry ->
    LogAction m ActualEntry
koreLogFilters koreLogOptions baseLogger =
    Colog.cfilter
        ( \entry ->
            filterEntry logEntries entry
                || filterSeverity logLevel entry
                || selectDebugApplyEquation debugApplyEquationOptions entry
                || selectDebugAttemptEquation debugAttemptEquationOptions entry
                || selectDebugEquation debugEquationOptions entry
        )
        baseLogger
  where
    KoreLogOptions{logLevel, logEntries} = koreLogOptions
    KoreLogOptions{debugApplyEquationOptions} = koreLogOptions
    KoreLogOptions{debugAttemptEquationOptions} = koreLogOptions
    KoreLogOptions{debugEquationOptions} = koreLogOptions

-- | Select the log entry types present in the active set.
filterEntry ::
    EntryTypes ->
    ActualEntry ->
    Bool
filterEntry logEntries ActualEntry{actualEntry} =
    typeOfSomeEntry actualEntry `elem` logEntries

-- | Select log entries with 'Severity' greater than or equal to the level.
filterSeverity ::
    Severity ->
    ActualEntry ->
    Bool
filterSeverity level ActualEntry{actualEntry = SomeEntry entry} =
    entrySeverity entry >= level

-- | Run a 'LoggerT' with the given options.
runKoreLog :: FilePath -> KoreLogOptions -> LoggerT IO a -> IO a
runKoreLog reportDirectory options loggerT =
    withLogger reportDirectory options $ runLoggerT loggerT

{- | The default Kore logger.

Creates a kore logger which:
  * adds timestamps
  * formats messages: "<exe-name>: [<timestamp>] <severity> (<entry-type>): <message>"
-}
makeKoreLogger ::
    forall io.
    MonadIO io =>
    ExeName ->
    TimeSpec ->
    TimestampsSwitch ->
    KoreLogFormat ->
    LogAction io Text ->
    LogAction io ActualEntry
makeKoreLogger exeName startTime timestampSwitch koreLogFormat logActionText =
    logActionText
        & contramap render
        & Colog.cmapM withTimestamp
  where
    render :: WithTimestamp -> Text
    render (WithTimestamp entry entryTime) =
        prettyActualEntry timestamp entry
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
    prettyActualEntry timestamp ActualEntry{actualEntry, entryContext}
        | OneLine <- koreLogFormat =
            Pretty.hsep $
                catMaybes [Just header, oneLineDoc actualEntry]
        | otherwise =
            (Pretty.vsep . concat)
                [ [header]
                , indent <$> context'
                , indent <$> [longDoc actualEntry]
                ]
      where
        header =
            (Pretty.hsep . catMaybes)
                [ Just exeName'
                , timestamp
                , Just severity'
                , Just (Pretty.parens $ type' actualEntry)
                ]
                <> Pretty.colon
        severity' = prettySeverity (entrySeverity actualEntry)
        type' entry =
            Pretty.pretty $
                lookupTextFromTypeWithError $
                    typeOfSomeEntry entry
        context' =
            entryContext
                & mapMaybe prettyContext
                & reverse
        prettyContext someEntry' =
            contextDoc someEntry'
                & fmap
                    ( \doc ->
                        Pretty.hsep [Pretty.parens typeName, doc <> Pretty.colon]
                    )
          where
            typeName = type' someEntry'
    indent = Pretty.indent 4

-- | Adds the current timestamp to a log entry.
withTimestamp :: MonadIO io => ActualEntry -> io WithTimestamp
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
    LogAction io ActualEntry
stderrLogger exeName startTime timestampsSwitch logFormat =
    makeKoreLogger exeName startTime timestampsSwitch logFormat Colog.logTextStderr

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
