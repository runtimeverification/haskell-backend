{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.SQLite
    ( LogSQLiteOptions (..)
    , parseLogSQLiteOptions
    , withLogSQLite
    ) where

import Colog
    ( unLogAction
    )
import qualified Control.Monad.Catch as Exception
import qualified Control.Monad.Extra as Monad
import Control.Monad.Reader
    ( runReaderT
    )
import Data.Default
import qualified Data.Foldable as Foldable
import Data.Proxy
import qualified Database.SQLite.Simple as SQLite
import qualified Options.Applicative as Options
import qualified System.Directory as Directory

import Kore.Log.DebugAppliedRule
    ( DebugAppliedRule
    )
import Kore.Log.DebugEvaluateCondition
    ( DebugEvaluateCondition
    )
import Kore.Log.WarnBottomHook
    ( WarnBottomHook
    )
import Kore.Log.WarnFunctionWithoutEvaluators
    ( WarnFunctionWithoutEvaluators
    )
import Kore.Log.WarnSimplificationWithRemainder
    ( WarnSimplificationWithRemainder
    )
import Log
import SQL
    ( SQL
    )
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
            Monad.whenM
                (Directory.doesPathExist filePath)
                (Directory.removeFile filePath)
            Exception.bracket (SQLite.open filePath) SQLite.close $ \conn -> do
                runReaderT (SQL.getSQLT declareEntries) conn
                cont (lowerLogAction conn logSQLite)
  where
    LogSQLiteOptions { sqlog } = options
    lowerLogAction conn logAction =
        LogAction $ \entry -> do
            let sqlt = unLogAction logAction entry
            runReaderT (SQL.getSQLT sqlt) conn

declareEntries :: SQL ()
declareEntries = foldMapEntries SQL.createTable

logSQLite :: LogAction SQL SomeEntry
logSQLite =
    foldMapEntries logEntry
  where
    logEntry
        :: forall entry
        .  (Entry entry, SQL.Table entry)
        => Proxy entry
        -> LogAction SQL SomeEntry
    logEntry _ = LogAction (maybeInsertRow . fromEntry @entry)

    maybeInsertRow :: SQL.Table entry => Maybe entry -> SQL ()
    maybeInsertRow = Foldable.traverse_ SQL.insertRow

foldMapEntries
    :: Monoid r
    => (forall entry. (Entry entry, SQL.Table entry) => Proxy entry -> r)
    -> r
foldMapEntries mapEntry =
    mconcat
        [ mapEntry (Proxy @DebugAppliedRule)
        , mapEntry (Proxy @DebugEvaluateCondition)
        , mapEntry (Proxy @WarnBottomHook)
        , mapEntry (Proxy @WarnFunctionWithoutEvaluators)
        , mapEntry (Proxy @WarnSimplificationWithRemainder)
        ]
