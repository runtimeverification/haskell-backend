module Kore.Log.SQLite
    ( LogSQLiteOptions (..)
    , parseLogSQLiteOptions
    , withLogSQLite
    ) where

import qualified Control.Monad as Monad
import qualified Control.Monad.Catch as Exception
import qualified Control.Monad.Extra as Extra
import Data.Default
import Data.Proxy
import qualified Database.SQLite.Simple as SQLite
import qualified Options.Applicative as Options
import qualified System.Directory as Directory

import Kore.Log.DebugAppliedRule
    ( DebugAppliedRule
    )
import Kore.Log.InfoEvaluateCondition
    ( InfoEvaluateCondition
    )
import Kore.Log.WarnBottomHook
    ( WarnBottomHook
    )
import Kore.Log.WarnFunctionWithoutEvaluators
    ( WarnFunctionWithoutEvaluators
    )
import Log
import qualified SQL

newtype LogSQLiteOptions =
    LogSQLiteOptions
    { sqlog :: Maybe FilePath
    -- ^ Filename for the structured query log.
    }
    deriving (Eq, Show)

instance Default LogSQLiteOptions where
    def = LogSQLiteOptions Nothing

parseLogSQLiteOptions :: Options.Parser LogSQLiteOptions
parseLogSQLiteOptions =
    LogSQLiteOptions
    <$> Options.optional parseSQLog

parseSQLog :: Options.Parser FilePath
parseSQLog =
    Options.strOption info
  where
    info =
        mempty
        <> Options.long "sqlog"
        <> Options.metavar "FILENAME"
        <> Options.help "Write the structured query log to FILENAME."

withLogSQLite :: LogSQLiteOptions -> (LogAction IO SomeEntry -> IO a) -> IO a
withLogSQLite options cont =
    case sqlog of
        Nothing -> cont mempty
        Just filePath -> do
            Extra.whenM (Directory.doesPathExist filePath)
                (Directory.removeFile filePath)
            Exception.bracket (SQLite.open filePath) SQLite.close $ \conn -> do
                declareEntries conn
                cont (logSQLite conn)
  where
    LogSQLiteOptions { sqlog } = options

declareEntries :: SQLite.Connection -> IO ()
declareEntries conn = foldMapEntries (SQL.createTable conn)

logSQLite :: SQLite.Connection -> LogAction IO SomeEntry
logSQLite conn =
    foldMapEntries logEntry
  where
    logEntry
        :: forall entry
        .  (Entry entry, SQL.Table entry)
        => Proxy entry
        -> LogAction IO SomeEntry
    logEntry _ = LogAction (maybeInsertRow . fromEntry @entry)

    maybeInsertRow :: SQL.Table entry => Maybe entry -> IO ()
    maybeInsertRow = maybe (return ()) (Monad.void . SQL.insertRow conn)

foldMapEntries
    :: Monoid r
    => (forall entry. (Entry entry, SQL.Table entry) => Proxy entry -> r)
    -> r
foldMapEntries mapEntry =
    mconcat
        [ mapEntry (Proxy @WarnBottomHook)
        , mapEntry (Proxy @DebugAppliedRule)
        , mapEntry (Proxy @InfoEvaluateCondition)
        , mapEntry (Proxy @WarnFunctionWithoutEvaluators)
        ]
