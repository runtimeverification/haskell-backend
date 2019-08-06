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
    ) where

import           Colog
                 ( LogAction (..) )
import qualified Colog
import           Control.Applicative
                 ( Alternative (..) )
import           Control.Concurrent.MVar
import           Control.Monad.Catch
                 ( MonadMask, bracket )
import           Control.Monad.IO.Class
                 ( MonadIO, liftIO )
import qualified Control.Monad.Trans as Trans
import           Data.Foldable
                 ( fold )
import qualified Data.Foldable as Fold
import           Data.Functor
                 ( void )
import           Data.Functor.Contravariant
                 ( contramap )
import           Data.List
                 ( intersperse )
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import           Data.String
                 ( IsString, fromString )
import           Data.Text
                 ( Text )
import qualified Data.Text as Text
import qualified Data.Text.Lazy as Text.Lazy
import           Data.Text.Lazy.Builder
                 ( Builder )
import qualified Data.Text.Lazy.Builder as Builder
import           Data.Time.Clock
                 ( getCurrentTime )
import           Data.Time.Format
                 ( defaultTimeLocale, formatTime )
import           Data.Time.LocalTime
                 ( LocalTime, getCurrentTimeZone, utcToLocalTime )
import           GHC.Stack
                 ( CallStack, getCallStack, popCallStack, prettyCallStack )
import           Options.Applicative
                 ( Parser, help, long, maybeReader, option )
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
data LogMessageWithTimestamp = LogMessageWithTimestamp LogMessage LocalTime

-- | Generates an appropriate logger for the given 'KoreLogOptions'. It uses
-- the CPS style because some outputters require cleanup (e.g. files).
withLogger
    :: Trans.MonadIO m
    => KoreLogOptions
    -> (LogAction m LogMessage -> IO a)
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
            <> help "Log type: None, StdOut, FileText"
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
            <> help "Log level: Debug, Info, Warning, Error, or Critical"
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
    -> LogAction m LogMessage
makeKoreLogger severity scopeSet logToText =
    Colog.cfilter (\(LogMessage _ logSeverity logScope _) -> logSeverity >= severity && logScope `member` scopeSet)
        . Colog.cmapM addTimeStamp
        $ contramap messageToText logToText
  where
    addTimeStamp :: LogMessage -> m LogMessageWithTimestamp
    addTimeStamp msg =
        LogMessageWithTimestamp msg <$> getLocalTime

    messageToText :: LogMessageWithTimestamp -> Text
    messageToText
        (LogMessageWithTimestamp
                (LogMessage message severity' scope callstack)
            localTime
        )
            = Text.Lazy.toStrict . Builder.toLazyText
                $ "["
                <> Builder.fromString (show severity')
                <> "] ["
                <> formatLocalTime "%Y-%m-%d %H:%M:%S%Q" localTime
                <> "] ["
                <> scopeToBuilder scope
                <> "]: "
                <> Builder.fromText message
                <> " ["
                <> formatCallStack callstack
                <> "]"

    scopeToBuilder :: [Scope] -> Builder
    scopeToBuilder =
        fold
            . intersperse "."
            . fmap (Builder.fromText . unScope)

    formatCallStack :: CallStack -> Builder
    formatCallStack cs
        | length (getCallStack cs) <= 1 = mempty
        | otherwise                    = callStackToBuilder cs

    callStackToBuilder :: CallStack -> Builder
    callStackToBuilder = Builder.fromString . prettyCallStack . popCallStack

    member :: [Scope] -> Set Scope -> Bool
    member s set
      | Set.null set = True
      | otherwise    = Fold.any (`Set.member` set) s

-- Helper to get the local time in 'MonadIO'.
getLocalTime :: MonadIO m => m LocalTime
getLocalTime =
    liftIO $ utcToLocalTime <$> getCurrentTimeZone <*> getCurrentTime

-- Formats the local time using the provided format string.
formatLocalTime :: IsString s => String -> LocalTime -> s
formatLocalTime format = fromString . formatTime defaultTimeLocale format

emptyLogger :: Applicative m => LogAction m msg
emptyLogger = mempty

stderrLogger :: MonadIO m => Severity -> Set Scope -> LogAction m LogMessage
stderrLogger logLevel logScopes = makeKoreLogger logLevel logScopes Colog.logTextStderr

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
