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
    , warningsToErrors
    ) where

import Prelude.Kore

import Colog
    ( LogAction (..)
    )
import qualified Colog
import Control.Concurrent
    ( killThread
    , myThreadId
    )
import Control.Concurrent.Async
    ( Async
    , async
    , wait
    )
import Control.Concurrent.MVar
import Control.Concurrent.STM
    ( TChan
    , atomically
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
    , bracket
    , catch
    , finally
    )
import Control.Monad.Cont
    ( ContT (..)
    , runContT
    )
import Control.Monad.Reader
    ( runReaderT
    , withReaderT
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
import qualified Data.Text as Text
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
import qualified GHC.Stack as GHC

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
-- the CPS style because some outputters require cleanup, e.g. files).
withLogger
    :: KoreLogOptions
    -> (LogAction IO SomeEntry -> IO a)
    -> IO a
withLogger koreLogOptions =
    runContT
        ( do
            mainLogger <- ContT $ withMainLogger koreLogOptions
            let KoreLogOptions { debugSolverOptions } = koreLogOptions
            smtSolverLogger <- ContT $ withSmtSolverLogger debugSolverOptions
            let KoreLogOptions { logSQLiteOptions } = koreLogOptions
            logSQLite <- ContT $ withLogSQLite logSQLiteOptions
            return $ mainLogger <> smtSolverLogger <> logSQLite
        )
        -- (action . Colog.cmap (warningsToErrors warnings))
  where
    KoreLogOptions { warnings } = koreLogOptions

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
        (mapDebugAxiomEvaluation debugAxiomEvaluationOptions)
        baseLogger
  where
    KoreLogOptions { debugAxiomEvaluationOptions } = koreLogOptions
    KoreLogOptions { warnings } = koreLogOptions
    f AsErrors e
        | entrySeverity e == Warning =
            error . show . longDoc $ e
        | otherwise = e
    f _ e = e

warningsToErrors
    :: Warnings
    -> SomeEntry
    -> SomeEntry
warningsToErrors AsWarnings entry = entry
warningsToErrors AsErrors (SomeEntry entry)
    | entrySeverity entry == Warning =
        toEntry LogMessage
            { message = Text.pack . show . longDoc $ entry
            , severity = Error
            , callstack = GHC.emptyCallStack
            }
    | otherwise = SomeEntry entry

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
runLoggerT options loggerT = do
    let runLogger = runReaderT . getLoggerT $ loggerT
    withLogger options $ \logger -> do
        (asyncThread, modifiedLogger) <- concurrentLogger logger warnings
        finally
            (runLogger modifiedLogger)
            (wait asyncThread)
  where
    f = withReaderT (Colog.cmap $ warningsToErrors warnings)
    KoreLogOptions { warnings } = options

concurrentLogger :: Entry a => LogAction IO a -> Warnings -> IO (Async (), LogAction IO a)
concurrentLogger logger warningType = do
    tChan <- newTChanIO
    mainId <- myThreadId
    asyncThread <-
        async $ catch
            (runLoggerThread tChan mainId warningType)
            (\BlockedIndefinitelyOnSTM -> return ())
    return (asyncThread, writeTChanLogger tChan)
  where
    runLoggerThread tChan mainId warningType =
        forever $ do
              val <- atomically $ readTChan tChan
              if entrySeverity val == Warning && warningType == AsErrors
                  then killThread mainId
                  else logger Colog.<& val

writeTChanLogger :: TChan a -> LogAction IO a
writeTChanLogger tChan =
    LogAction $ \msg -> atomically $ writeTChan tChan msg

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
    Colog.LogAction $ bracket acquire release . worker
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
