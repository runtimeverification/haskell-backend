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
import Control.Concurrent.MVar
import Control.Monad.Catch
    ( MonadMask
    , bracket
    )
import Control.Monad.IO.Class
    ( MonadIO
    , liftIO
    )
import Control.Monad.Reader
    ( runReaderT
    )
import qualified Control.Monad.Trans as Trans
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
    , help
    , long
    , maybeReader
    , option
    )
import qualified Text.Megaparsec as Parser
import qualified Text.Megaparsec.Char as Parser

import Kore.Logger

-- | 'KoreLogType' is passed via command line arguments and decides if and how
-- the logger will operate.
data KoreLogType
    = LogNone
    -- ^ do not log when no '--log' is passed
    | LogStdErr
    -- ^ log to StdOut when '--log StdOut' is passed
    | LogFileText
    -- ^ log to "./kore-(date).log" when '--log FileText' is passed
    deriving (Read)

-- | 'KoreLogOptions' is the top-level options type for logging, containing the
-- desired output method and the minimum 'Severity'.
data KoreLogOptions = KoreLogOptions
    { logType   :: KoreLogType
    -- ^ desired output method, see 'KoreLogType'
    , logLevel  :: Severity
    -- ^ minimal log level, passed via "--log-level"
    , logScopes :: Set Scope
    -- ^ scopes to show, empty means show all
    }

-- | Internal type used to add timestamps to a 'LogMessage'.
data WithTimestamp = WithTimestamp SomeEntry LocalTime

instance Pretty.Pretty WithTimestamp where
    pretty (WithTimestamp entry time) =
        Pretty.brackets formattedTime <> Pretty.pretty entry
      where
        formattedTime = formatLocalTime "%Y-%m-%d %H:%M:%S%Q" time

instance Entry WithTimestamp where
    shouldLog
        minSeverity
        currentScope
        (WithTimestamp (SomeEntry entry) _)
      = shouldLog minSeverity currentScope entry

-- | Generates an appropriate logger for the given 'KoreLogOptions'. It uses
-- the CPS style because some outputters require cleanup (e.g. files).
withLogger
    :: Trans.MonadIO m
    => KoreLogOptions
    -> (LogAction m SomeEntry -> IO a)
    -> IO a
withLogger KoreLogOptions { logType, logLevel, logScopes } cont =
    case logType of
        LogNone     ->
            cont mempty
        LogStdErr   ->
            cont (stderrLogger logLevel logScopes)
        LogFileText -> do
            fileName <- getKoreLogFileName
            Colog.withLogTextFile fileName
                $ cont . makeKoreLogger logLevel logScopes
  where
    getKoreLogFileName :: IO String
    getKoreLogFileName = do
        currentTimeDate <- getLocalTime
        pure
            $ "kore-"
            <> formatLocalTime "%Y-%m-%d-%H-%M-%S" currentTimeDate
            <> ".log"

-- | Run a 'LoggerT' with the given options.
runLoggerT :: KoreLogOptions -> LoggerT IO a -> IO a
runLoggerT options = withLogger options . runReaderT . getLoggerT

-- Parser for command line log options.
parseKoreLogOptions :: Parser KoreLogOptions
parseKoreLogOptions =
    KoreLogOptions
    <$> (parseType <|> pure LogNone)
    <*> (parseLevel <|> pure Warning)
    <*> (parseScope <|> pure mempty)
  where
    parseType =
        option
            (maybeReader parseTypeString)
            $ long "log"
            <> help "Log type: none, stdout, filetext"
    parseTypeString =
        \case
            "none"     -> pure LogNone
            "stdout"   -> pure LogStdErr
            "filetext" -> pure LogFileText
            _          -> Nothing
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
    parseScope =
        option
            parseCommaSeparatedScopes
            $ long "log-scope"
            <> help "Log scope"
    parseCommaSeparatedScopes = maybeReader $ Parser.parseMaybe scopeParser
    scopeParser :: Parser.Parsec String String (Set Scope)
    scopeParser = do
        args <- many itemParser
        pure . Set.fromList $ args
    itemParser :: Parser.Parsec String String Scope
    itemParser = do
        argument <- some (Parser.noneOf [','])
        _ <- void (Parser.char ',') <|> Parser.eof
        pure . Scope . Text.pack $ argument

-- Creates a kore logger which:
--     * filters messages that have lower severity than the provided severity
--     * adds timestamps
--     * formats messages: "[<severity>][<localTime>][<scope>]: <message>"
makeKoreLogger
    :: forall m
    .  MonadIO m
    => Severity
    -> Set Scope
    -> LogAction m Text
    -> LogAction m SomeEntry
makeKoreLogger minSeverity currentScope logToText =
    Colog.cfilter (withSomeEntry (shouldLog minSeverity currentScope))
        . Colog.cmapM withTimestamp
        $ contramap messageToText logToText
  where
    messageToText :: WithTimestamp -> Text
    messageToText =
        Pretty.renderStrict
        . Pretty.layoutPretty Pretty.defaultLayoutOptions
        . Pretty.pretty

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

stderrLogger :: MonadIO m => Severity -> Set Scope -> LogAction m SomeEntry
stderrLogger logLevel logScopes =
    makeKoreLogger logLevel logScopes Colog.logTextStderr

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
