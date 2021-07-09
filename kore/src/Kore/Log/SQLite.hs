{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause

Record log entries to a SQLite database.
-}
module Kore.Log.SQLite (
    LogSQLiteOptions (..),
    parseLogSQLiteOptions,
    withLogSQLite,
) where

import qualified Control.Monad.Catch as Exception
import qualified Control.Monad.Extra as Monad
import Control.Monad.Reader (
    runReaderT,
 )
import Data.Default
import Data.Proxy
import qualified Database.SQLite.Simple as SQLite
import Kore.Log.DebugEvaluateCondition (
    DebugEvaluateCondition,
 )
import Kore.Log.DebugSubstitutionSimplifier (
    DebugSubstitutionSimplifier,
 )
import Kore.Log.ErrorBottomTotalFunction (
    ErrorBottomTotalFunction,
 )
import Kore.Log.WarnFunctionWithoutEvaluators (
    WarnFunctionWithoutEvaluators,
 )
import Kore.Log.WarnSymbolSMTRepresentation (
    WarnSymbolSMTRepresentation,
 )
import Log (
    ActualEntry,
    Entry,
    LogAction (..),
    SomeEntry,
    fromEntry,
    fromLogAction,
 )
import qualified Options.Applicative as Options
import Prelude.Kore
import SQL (
    SQL,
 )
import qualified SQL
import qualified System.Directory as Directory

-- | @LogSQLiteOptions@ are the command-line options for the SQLite logger.
newtype LogSQLiteOptions = LogSQLiteOptions
    { -- | Filename for the structured query log.
      sqlog :: Maybe FilePath
    }
    deriving stock (Eq, Show)

instance Default LogSQLiteOptions where
    def = LogSQLiteOptions Nothing

parseLogSQLiteOptions :: Options.Parser LogSQLiteOptions
parseLogSQLiteOptions =
    LogSQLiteOptions
        <$> Options.optional parseSQLog

-- | Parse the command-line argument that takes the SQLite database's filename.
parseSQLog :: Options.Parser FilePath
parseSQLog =
    Options.strOption info
  where
    info =
        mempty
            <> Options.long "sqlog"
            <> Options.metavar "FILENAME"
            <> Options.help "Write the structured query log to FILENAME."

{- | Run the continuation with a 'LogAction' to send entries to the database.

The logger is configured according to the given
'LogSQLiteOptions'. @withLogSQLite@ opens and closes the database connection
automatically.
-}
withLogSQLite ::
    LogSQLiteOptions ->
    -- | Continuation
    (LogAction IO ActualEntry -> IO a) ->
    IO a
withLogSQLite options cont =
    case sqlog of
        Nothing -> cont mempty
        Just filePath -> do
            Monad.whenM
                (Directory.doesPathExist filePath)
                (Directory.removeFile filePath)
            Exception.bracket (SQLite.open filePath) SQLite.close $ \conn -> do
                runReaderT (SQL.getSQL declareEntries) conn
                cont (lowerLogAction conn logSQLite)
  where
    LogSQLiteOptions{sqlog} = options
    lowerLogAction conn logAction =
        LogAction $ \entry -> do
            let sqlt = unLogAction logAction entry
            runReaderT (SQL.getSQL sqlt) conn

{- | 'foldMap' over the known 'SQL.Table' 'Entry' types.

These are the only types of 'Entry' that can be logged to the database.

See also: 'declareEntries', 'logSQLite'
-}
foldMapEntries ::
    Monoid r =>
    (forall entry. (Entry entry, SQL.Table entry) => Proxy entry -> r) ->
    r
foldMapEntries mapEntry =
    mconcat
        [ mapEntry (Proxy @DebugEvaluateCondition)
        , mapEntry (Proxy @DebugSubstitutionSimplifier)
        , mapEntry (Proxy @ErrorBottomTotalFunction)
        , mapEntry (Proxy @WarnFunctionWithoutEvaluators)
        , mapEntry (Proxy @WarnSymbolSMTRepresentation)
        ]

-- | Declare the SQL tables for all known 'SQL.Table' 'Entry' types.
declareEntries :: SQL ()
declareEntries = foldMapEntries SQL.createTable

{- | Log 'SomeEntry' to the database.

If the 'Entry' cannot be entered in the database, it is ignored.

@logSQLite@ is a 'LogAction' in the 'SQL' context, which requires that the
database is already connected. See 'withLogSQLite' to obtain a 'LogAction' in
'IO'.
-}
logSQLite :: LogAction SQL ActualEntry
logSQLite =
    foldMapEntries (fromLogAction @SomeEntry . logEntry)
  where
    logEntry ::
        forall entry.
        (Entry entry, SQL.Table entry) =>
        Proxy entry ->
        LogAction SQL SomeEntry
    logEntry _ = LogAction (maybeInsertRow . fromEntry @entry)

    maybeInsertRow :: SQL.Table entry => Maybe entry -> SQL ()
    maybeInsertRow = traverse_ SQL.insertRow
