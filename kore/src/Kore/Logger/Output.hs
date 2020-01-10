{-|
Module      : Kore.Logger.Output
Description : Logger helpers and internals needed for Main.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
-}

module Kore.Logger.Output
    ( KoreLogType (..)
    , KoreLogOptions (..)
    , EntryTypes
    , TimestampsSwitch (..)
    , koreLogFilters
    , withLogger
    , parseKoreLogOptions
    , emptyLogger
    , stderrLogger
    , swappableLogger
    , makeKoreLogger
    , Colog.logTextStderr
    , Colog.logTextHandle
    , module Kore.Logger
    , runLoggerT
    ) where

import Colog
    ( LogAction (..)
    )
import qualified Colog
import Control.Applicative
    ( Alternative (..)
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
import Control.Monad.IO.Class
    ( MonadIO
    , liftIO
    )
import Control.Monad.Reader
    ( runReaderT
    )
import Data.Functor
    ( void
    )
import Data.Functor.Contravariant
    ( contramap
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
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
import Options.Applicative
    ( Parser
    , flag'
    , help
    , helpDoc
    , long
    , maybeReader
    , option
    )
import qualified Options.Applicative.Help.Pretty as OptPretty
import qualified Text.Megaparsec as Parser
import qualified Text.Megaparsec.Char as Parser
import Type.Reflection
    ( SomeTypeRep (..)
    )

import Kore.Logger
import Kore.Logger.DebugAppliedRule
import Kore.Logger.DebugAxiomEvaluation
    ( DebugAxiomEvaluationOptions
    , filterDebugAxiomEvaluation
    , parseDebugAxiomEvaluationOptions
    )
import Kore.Logger.DebugSolver
    ( DebugSolverOptions (DebugSolverOptions)
    , parseDebugSolverOptions
    , solverTranscriptLogger
    )
import qualified Kore.Logger.DebugSolver as DebugSolver.DoNotUse
import Kore.Logger.Registry
    ( getEntryTypesAsText
    , lookupTextFromTypeWithError
    , parseEntryType
    , toSomeEntryType
    )

-- | 'KoreLogType' is passed via command line arguments and decides if and how
-- the logger will operate.
data KoreLogType
    = LogStdErr
    -- ^ Log to stderr
    | LogFileText FilePath
    -- ^ Log to specified file when '--log <filename>' is passed.
    deriving (Eq, Show)

type EntryTypes = Set SomeTypeRep

-- | 'KoreLogOptions' is the top-level options type for logging, containing the
-- desired output method and the minimum 'Severity'.
data KoreLogOptions = KoreLogOptions
    { logType   :: KoreLogType
    -- ^ desired output method, see 'KoreLogType'
    , logLevel  :: Severity
    -- ^ minimal log level, passed via "--log-level"
    , timestampsSwitch :: TimestampsSwitch
    -- ^ enable or disable timestamps
    , logEntries :: EntryTypes
    -- ^ extra entries to show, ignoring 'logLevel'
    , debugAppliedRuleOptions :: DebugAppliedRuleOptions
    , debugAxiomEvaluationOptions :: DebugAxiomEvaluationOptions
    , debugSolverOptions :: DebugSolverOptions
    }
    deriving (Eq, Show)

-- | Internal type used to add timestamps to a 'LogMessage'.
data WithTimestamp = WithTimestamp SomeEntry LocalTime

-- | Generates an appropriate logger for the given 'KoreLogOptions'. It uses
-- the CPS style because some outputters require cleanup (e.g. files).
withLogger
    :: KoreLogOptions
    -> (LogAction IO SomeEntry -> IO a)
    -> IO a
withLogger
    koreLogOptions@KoreLogOptions { debugSolverOptions }
    continue
  =
    withMainLogger koreLogOptions
    $ \mainLogger -> withSmtSolverLogger debugSolverOptions
    $ \smtSolverLogger -> continue (mainLogger <> smtSolverLogger)

withMainLogger :: KoreLogOptions -> (LogAction IO SomeEntry -> IO a) -> IO a
withMainLogger
    koreLogOptions@KoreLogOptions { logType, timestampsSwitch } continue =
        case logType of
            LogStdErr -> continue
                $ koreLogFilters koreLogOptions (stderrLogger timestampsSwitch)
            LogFileText filename ->
                Colog.withLogTextFile filename
                $ continue
                . koreLogFilters koreLogOptions
                . makeKoreLogger timestampsSwitch

withSmtSolverLogger
    :: DebugSolverOptions -> (LogAction IO SomeEntry -> IO a) -> IO a
withSmtSolverLogger DebugSolverOptions {logFile} continue =
    case logFile of
        Nothing -> continue mempty
        Just filename -> Colog.withLogTextFile filename
            $ continue . solverTranscriptLogger

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
        (asyncThread, modifiedLogger) <- concurrentLogger logger
        finally
            (runLogger modifiedLogger)
            (wait asyncThread)

concurrentLogger :: LogAction IO a -> IO (Async (), LogAction IO a)
concurrentLogger logger = do
    tChan <- newTChanIO
    asyncThread <-
        async $ catch
            (runLoggerThread tChan)
            (\BlockedIndefinitelyOnSTM -> return ())
    return (asyncThread, writeTChanLogger tChan)
  where
    runLoggerThread tChan =
        forever $ do
              val <- atomically $ readTChan tChan
              logger Colog.<& val

writeTChanLogger :: TChan a -> LogAction IO a
writeTChanLogger tChan =
    LogAction $ \msg -> atomically $ writeTChan tChan msg

-- Parser for command line log options.
parseKoreLogOptions :: Parser KoreLogOptions
parseKoreLogOptions =
    KoreLogOptions
    <$> (parseType <|> pure LogStdErr)
    <*> (parseLevel <|> pure Warning)
    <*> (parseTimestampsOption <|> pure TimestampsEnable)
    <*> (mconcat <$> many parseEntries)
    <*> parseDebugAppliedRuleOptions
    <*> parseDebugAxiomEvaluationOptions
    <*> parseDebugSolverOptions
  where
    parseType :: Parser KoreLogType
    parseType =
        option
            (maybeReader parseTypeString)
            $ long "log"
            <> help "Name of the log file"

      where
        parseTypeString filename = pure $ LogFileText filename

    parseLevel =
        option
            (maybeReader parseSeverity)
            $ long "log-level"
            <> help "Log level: debug, info, warning, error, or critical"
    parseSeverity =
        \case
            "debug"    -> pure Debug
            "info"     -> pure Info
            "warning"  -> pure Warning
            "error"    -> pure Error
            "critical" -> pure Critical
            _          -> Nothing
    parseTimestampsOption :: Parser TimestampsSwitch
    parseTimestampsOption = parseTimestampsEnable <|> parseTimestampsDisable
      where
        parseTimestampsEnable =
            flag' TimestampsEnable
                (  long "enable-log-timestamps"
                <> help "Enable log timestamps" )
        parseTimestampsDisable =
            flag' TimestampsDisable
                (  long "disable-log-timestamps"
                <> help "Disable log timestamps" )

    parseEntries =
        option
            parseCommaSeparatedEntries
            $ long "log-entries"
            <> helpDoc
               ( Just listOfEntries )

    parseCommaSeparatedEntries = maybeReader $ Parser.parseMaybe entryParser
    entryParser :: Parser.Parsec String String EntryTypes
    entryParser = do
        args <- many itemParser
        pure . Set.fromList $ args
    itemParser :: Parser.Parsec String String SomeTypeRep
    itemParser = do
        argument <- some (Parser.noneOf [',', ' '])
        _ <- void (Parser.char ',') <|> Parser.eof
        parseEntryType . Text.pack $ argument

listOfEntries :: OptPretty.Doc
listOfEntries =
    OptPretty.vsep $
        [ "Log entries: logs entries of supplied types"
        , "Available entry types:"
        ]
        <> fmap
            (OptPretty.indent 4 . OptPretty.text . Text.unpack)
            getEntryTypesAsText

-- | Enable or disable timestamps
data TimestampsSwitch = TimestampsEnable | TimestampsDisable
    deriving (Eq, Show)

-- Creates a kore logger which:
--     * adds timestamps
--     * formats messages: "[<severity>][<localTime>][<scope>]: <message>"
makeKoreLogger
    :: forall m
    .  MonadIO m
    => TimestampsSwitch
    -> LogAction m Text
    -> LogAction m SomeEntry
makeKoreLogger timestampSwitch logToText =
    Colog.cmapM withTimestamp
    $ contramap messageToText logToText
  where
    messageToText :: WithTimestamp -> Text
    messageToText (WithTimestamp entry localTime) =
        Pretty.renderStrict
        . Pretty.layoutPretty Pretty.defaultLayoutOptions
        $ timestamp <> defaultLogPretty entry
      where
        timestamp = case timestampSwitch of
            TimestampsEnable -> Pretty.brackets (formattedTime localTime)
            TimestampsDisable -> mempty
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

stderrLogger :: MonadIO io => TimestampsSwitch -> LogAction io SomeEntry
stderrLogger timestampsSwitch =
    makeKoreLogger timestampsSwitch Colog.logTextStderr

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
    Pretty.hsep
        [ Pretty.brackets (Pretty.pretty . entrySeverity $ entry)
        , ":"
        , Pretty.brackets
            . Pretty.pretty
            . lookupTextFromTypeWithError
            . toSomeEntryType
            $ entry
        , ":"
        , Pretty.pretty entry
        ]
