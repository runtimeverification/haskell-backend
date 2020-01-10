module Kore.Log.SQLite
    ( LogSQLiteOptions (..)
    , parseLogSQLiteOptions
    , withLogSQLite
    ) where

import qualified Control.Monad.Catch as Exception
import Data.Default
import Data.Proxy
import qualified Database.SQLite.Simple as SQLite
import qualified Options.Applicative as Options

import Kore.Log.WarnBottomHook
    ( WarnBottomHook
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
        Just filePath ->
            Exception.bracket (SQLite.open filePath) SQLite.close $ \conn -> do
                declareEntries conn
                cont (logSQLite conn)
  where
    LogSQLiteOptions { sqlog } = options

declareEntries :: SQLite.Connection -> IO ()
declareEntries conn = do
    SQL.createTable conn $ Proxy @WarnBottomHook

-- TODO (thomas.tuegel): Implement me!
logSQLite :: SQLite.Connection -> LogAction IO SomeEntry
logSQLite _ = mempty
