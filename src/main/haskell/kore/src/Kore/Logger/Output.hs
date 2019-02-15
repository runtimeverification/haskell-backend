{-|
Module      : Kore.Logger.Output
Description : Logger helpers and internals needed for Main.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : vladimir.ciobanu@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Logger.Output
    ( KoreLogType (..)
    , KoreLogOptions (..)
    , withLogger
    , parseKoreLogOptions
    ) where

import           Colog
                 ( LogAction (..) )
import qualified Colog as Colog
import           Control.Applicative
                 ( Alternative (..) )
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import qualified Control.Monad.Trans as Trans
import           Data.Functor.Contravariant
                 ( contramap )
import           Data.String
                 ( IsString, fromString )
import           Data.Text
                 ( Text )
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Text.Lazy.Builder as Builder
import           Data.Time.Clock
                 ( getCurrentTime )
import           Data.Time.Format
                 ( defaultTimeLocale, formatTime )
import           Data.Time.LocalTime
                 ( LocalTime, getCurrentTimeZone, utcToLocalTime )
import           Kore.Logger
import           Options.Applicative
                 ( Parser, auto, help, long, option, str )
import           Text.Read
                 ( readMaybe )

-- | 'KoreLogType' is passed via command line arguments and decides if and how
-- the logger will operate.
data KoreLogType
    = LogNone
    -- ^ do not log when no '--log' is passed
    | LogStdOut
    -- ^ log to StdOut when '--log StdOut' is passed
    | LogFileText
    -- ^ log to "./kore-(date).log" when '--log FileText' is passed
    deriving (Read)

-- | 'KoreLogOptions' is the top-level options type for logging, containing the
-- desired output method and the minimum 'Severity'.
data KoreLogOptions = KoreLogOptions
    { logType  :: KoreLogType
    -- ^ desired output method, see 'KoreLogType'
    , logLevel :: Severity
    -- ^ minimal log level, passed via "--log-level"
    }

-- | Internal type used to add timestamps to a 'LogMessage'.
data LogMessageWithTimestamp = LogMessageWithTimestamp LogMessage LocalTime

-- | Generates an appropriate logger for the given 'KoreLogOptions'. It uses
-- the CPS style because some outputters require cleanup (e.g. files).
withLogger
    :: Trans.MonadIO m
    => KoreLogOptions
    -> (LogAction m LogMessage -> IO a)
    -> IO a
withLogger KoreLogOptions { logType, logLevel } cont =
    case logType of
        LogNone     ->
            cont mempty
        LogStdOut   ->
            cont $ makeKoreLogger logLevel Colog.logTextStdout
        LogFileText -> do
            fileName <- getKoreLogFileName
            Colog.withLogTextFile fileName
                $ cont . makeKoreLogger logLevel
  where
    getKoreLogFileName :: IO String
    getKoreLogFileName = do
        currentTimeDate <- getLocalTime
        pure
            $ "kore-"
            <> formatLocalTime "%Y-%m-%d-%H-%M-%S" currentTimeDate
            <> ".log"

-- Parser for command line log options.
parseKoreLogOptions :: Parser KoreLogOptions
parseKoreLogOptions =
    KoreLogOptions
    <$> (parseType <|> pure LogNone)
    <*> (parseLevel <|> pure Info)
  where
    parseType =
        option
            parseTypeString
            $ long "log"
            <> help "Log type: None, StdOut, FileText"
    -- TODO(Vladimir): This should be implemented as
    -- `Read deriving via StripPrefix "Log"`
    parseTypeString = do
        t <- str
        pure $ maybe LogNone id $ readMaybe ("Log" ++ t)
    parseLevel =
        option
            auto
            $ long "log-level"
            <> help "Log level: Debug, Info, Warning, Error, or Critical"

-- Creates a kore logger which:
--     * filters messages that have lower severity than the provided severity
--     * adds timestamps
--     * formats messages: "[<severity>][<localTime>][<scope>]: <message>"
makeKoreLogger
    :: forall m
    .  MonadIO m
    => Severity
    -> LogAction m Text
    -> LogAction m LogMessage
makeKoreLogger severity logToText =
    Colog.cfilter (\(LogMessage _ s _) -> s >= severity)
        . Colog.cmapM addTimeStamp
        $ contramap messageToText logToText
  where
    addTimeStamp :: LogMessage -> m LogMessageWithTimestamp
    addTimeStamp msg = do
        currentTimeDate <- getLocalTime
        pure $ LogMessageWithTimestamp msg currentTimeDate

    messageToText :: LogMessageWithTimestamp -> Text
    messageToText
        (LogMessageWithTimestamp
            (LogMessage message severity' scope)
            localTime
        )
            = Text.Lazy.toStrict . Builder.toLazyText
                $ "["
                <> Builder.fromString (show severity')
                <> "] ["
                <> formatLocalTime "%Y-%m-%d %H:%M:%S%Q" localTime
                <> "] ["
                <> Builder.fromText scope
                <> "]: "
                <> Builder.fromText message

-- Helper to get the local time in 'MonadIO'.
getLocalTime :: MonadIO m => m LocalTime
getLocalTime =
    liftIO $ utcToLocalTime <$> getCurrentTimeZone <*> getCurrentTime

-- Formats the local time using the provided format string.
formatLocalTime :: IsString s => String -> LocalTime -> s
formatLocalTime format = fromString . formatTime defaultTimeLocale format
