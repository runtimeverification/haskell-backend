{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}

module Kore.Log
    ( koreLogFilters
    , withLogger
    , emptyLogger
    , stderrLogger
    , swappableLogger
    , makeKoreLogger
    , Colog.logTextStderr
    , Colog.logTextHandle
    , runLoggerT
    , module Log
    , module KoreLogOptions
    ) where

import Prelude.Kore

import Colog
    ( LogAction (..)
    )
import qualified Colog
import Control.Concurrent.Async
    ( async
    )
import Control.Concurrent.Async as Async
import Control.Concurrent.MVar
import Control.Concurrent.STM
    ( atomically
    , newTChanIO
    , readTChan
    , writeTChan
    )
import Control.Exception
    ( BlockedIndefinitelyOnSTM (..)
    )
import Control.Monad
    ( forever
    )
import Control.Monad.Catch
    ( MonadMask
    )
import qualified Control.Monad.Catch as Exception
import Control.Monad.Cont
    ( ContT (..)
    , runContT
    )
import Control.Monad.Reader
    ( runReaderT
    )
import Data.Functor.Contravariant
    ( contramap
    )
import Data.String
    ( IsString
    , fromString
    )
import Data.Text
    ( Text
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.Text as Pretty
import Data.Time.Clock
    ( getCurrentTime
    )
import Data.Time.Format
    ( defaultTimeLocale
    , formatTime
    )
import Data.Time.LocalTime
    ( LocalTime
    , getCurrentTimeZone
    , utcToLocalTime
    )

import Kore.Log.DebugAppliedRule
import Kore.Log.DebugAxiomEvaluation
    ( filterDebugAxiomEvaluation
    , mapDebugAxiomEvaluation
    )
import Kore.Log.DebugSolver
    ( DebugSolverOptions (DebugSolverOptions)
    , solverTranscriptLogger
    )
import qualified Kore.Log.DebugSolver as DebugSolver.DoNotUse
import Kore.Log.KoreLogOptions as KoreLogOptions
import Kore.Log.Registry
    ( lookupTextFromTypeWithError
    , toSomeEntryType
    )
import Kore.Log.SQLite
import Log

-- | Internal type used to add timestamps to a 'LogMessage'.
data WithTimestamp = WithTimestamp SomeEntry LocalTime

-- | Generates an appropriate logger for the given 'KoreLogOptions'. It uses
-- the CPS style because some outputters require cleanup (e.g. files).
withLogger
    :: KoreLogOptions
    -> (LogAction IO SomeEntry -> IO a)
    -> IO a
withLogger koreLogOptions = runContT $ do
    mainLogger <- ContT $ withMainLogger koreLogOptions
    let KoreLogOptions { debugSolverOptions } = koreLogOptions
    smtSolverLogger <- ContT $ withSmtSolverLogger debugSolverOptions
    let KoreLogOptions { logSQLiteOptions } = koreLogOptions
    logSQLite <- ContT $ withLogSQLite logSQLiteOptions
    return $ mainLogger <> smtSolverLogger <> logSQLite

withMainLogger
    :: KoreLogOptions
    -> (LogAction IO SomeEntry -> IO a)
    -> IO a
withMainLogger
    koreLogOptions@KoreLogOptions { logType, timestampsSwitch, exeName }
    continue
  =
    case logType of
        LogStdErr -> continue
            $ koreLogTransformer koreLogOptions
            $ koreLogFilters koreLogOptions
                (stderrLogger exeName timestampsSwitch)
        LogFileText filename ->
            Colog.withLogTextFile filename
            $ continue
            . koreLogTransformer koreLogOptions
            . koreLogFilters koreLogOptions
            . makeKoreLogger exeName timestampsSwitch

withSmtSolverLogger
    :: DebugSolverOptions -> (LogAction IO SomeEntry -> IO a) -> IO a
withSmtSolverLogger DebugSolverOptions {logFile} continue =
    case logFile of
        Nothing -> continue mempty
        Just filename -> Colog.withLogTextFile filename
            $ continue . solverTranscriptLogger

koreLogTransformer
    :: KoreLogOptions
    -> LogAction m SomeEntry
    -> LogAction m SomeEntry
koreLogTransformer koreLogOptions baseLogger =
    Colog.cmap
        ( warningsToErrors warningSwitch
        . mapDebugAxiomEvaluation debugAxiomEvaluationOptions
        )
        baseLogger
  where
    KoreLogOptions { debugAxiomEvaluationOptions } = koreLogOptions
    KoreLogOptions { warningSwitch } = koreLogOptions
    warningsToErrors AsError entry
        | entrySeverity entry == Warning =
            error . show . longDoc $ entry
        | otherwise = entry
    warningsToErrors AsWarning entry = entry

koreLogFilters
    :: Applicative m
    => KoreLogOptions
    -> LogAction m SomeEntry
    -> LogAction m SomeEntry
koreLogFilters koreLogOptions baseLogger =
    Colog.cfilter
        (\entry ->
            filterEntry logEntries entry
            || filterSeverity logLevel entry
            || filterDebugAppliedRule debugAppliedRuleOptions entry
            || filterDebugAxiomEvaluation debugAxiomEvaluationOptions entry
        )
    baseLogger
  where
    KoreLogOptions { logLevel, logEntries } = koreLogOptions
    KoreLogOptions { debugAppliedRuleOptions } = koreLogOptions
    KoreLogOptions { debugAxiomEvaluationOptions } = koreLogOptions

{- | Select the log entry types present in the active set.
 -}
filterEntry
    :: EntryTypes
    -> SomeEntry
    -> Bool
filterEntry logEntries (SomeEntry entry) =
    toSomeEntryType entry `elem` logEntries

{- | Select log entries with 'Severity' greater than or equal to the level.
 -}
filterSeverity
    :: Severity
    -> SomeEntry
    -> Bool
filterSeverity level entry =
    entrySeverity entry >= level

-- | Run a 'LoggerT' with the given options.
runLoggerT :: KoreLogOptions -> LoggerT IO a -> IO a
runLoggerT options loggerT =
    withLogger options $ \logAction ->
    withAsyncLogger logAction $ \asyncLogAction ->
        runLogger (fromLogAction asyncLogAction)
  where
    runLogger = runReaderT . getLoggerT $ loggerT

withAsyncLogger
    :: LogAction IO a
    -> (LogAction IO a -> IO b)
    -> IO b
withAsyncLogger logAction continue = do
    tChan <- newTChanIO
    let asyncLogAction = LogAction (atomically . writeTChan tChan)
    logAsync <- async $ untilDone $ do
        a <- atomically $ readTChan tChan
        logAction Colog.<& a
    mainAsync <- async $ continue asyncLogAction
    (_, b) <- tryAgain $ Async.waitBoth logAsync mainAsync
    return b
  where
    handleBlockedIndefinitelyOnSTM handler =
        Exception.handle $ \BlockedIndefinitelyOnSTM -> handler
    ignore = return ()
    untilDone = handleBlockedIndefinitelyOnSTM ignore . forever
    tryAgain action = handleBlockedIndefinitelyOnSTM action action

-- Creates a kore logger which:
--     * adds timestamps
--     * formats messages: "[<severity>][<localTime>][<scope>]: <message>"
makeKoreLogger
    :: forall m
    .  MonadIO m
    => ExeName
    -> TimestampsSwitch
    -> LogAction m Text
    -> LogAction m SomeEntry
makeKoreLogger exeName timestampSwitch logToText =
    Colog.cmapM withTimestamp
    $ contramap messageToText logToText
  where
    messageToText :: WithTimestamp -> Text
    messageToText (WithTimestamp entry localTime) =
        Pretty.renderStrict
        . Pretty.layoutPretty Pretty.defaultLayoutOptions
        $ exeName' Pretty.<+> timestamp Pretty.<+> defaultLogPretty entry
      where
        timestamp = case timestampSwitch of
            TimestampsEnable -> Pretty.brackets (formattedTime localTime)
            TimestampsDisable -> mempty
        exeName' = Pretty.pretty exeName <> Pretty.colon
    formattedTime = formatLocalTime "%Y-%m-%d %H:%M:%S%Q"

-- | Adds the current timestamp to a log entry.
withTimestamp :: MonadIO io => SomeEntry -> io WithTimestamp
withTimestamp msg = WithTimestamp msg <$> getLocalTime

-- Helper to get the local time in 'MonadIO'.
getLocalTime :: MonadIO m => m LocalTime
getLocalTime =
    liftIO $ utcToLocalTime <$> getCurrentTimeZone <*> getCurrentTime

-- Formats the local time using the provided format string.
formatLocalTime :: IsString s => String -> LocalTime -> s
formatLocalTime format = fromString . formatTime defaultTimeLocale format

emptyLogger :: Applicative m => LogAction m msg
emptyLogger = mempty

stderrLogger
    :: MonadIO io
    => ExeName
    -> TimestampsSwitch
    -> LogAction io SomeEntry
stderrLogger exeName timestampsSwitch =
    makeKoreLogger exeName timestampsSwitch Colog.logTextStderr

{- | @swappableLogger@ delegates to the logger contained in the 'MVar'.

This allows the logger to be "swapped" during execution. (It also automatically
makes the logger thread-safe.)

 -}
swappableLogger
    :: (MonadIO m, MonadMask m)
    => MVar (LogAction m a)
    -> LogAction m a
swappableLogger mvar =
    Colog.LogAction $ Exception.bracket acquire release . worker
  where
    acquire = liftIO $ takeMVar mvar
    release = liftIO . putMVar mvar
    worker a logAction = Colog.unLogAction logAction a

defaultLogPretty :: SomeEntry -> Pretty.Doc ann
defaultLogPretty (SomeEntry entry) =
    header Pretty.<+> longDoc entry
  where
    severity = prettySeverity (entrySeverity entry)
    type' = Pretty.pretty (lookupTextFromTypeWithError $ toSomeEntryType entry)
    header = severity Pretty.<+> Pretty.parens type' <> Pretty.colon
