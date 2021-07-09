{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module SQL.SQL (
    SQL (..),
    runSQL,
    execute_,
    execute,
    executeNamed,
    query,
    queryNamed,
    lastInsertRowId,

    -- * Re-exports
    Query,
    SQLData (..),
) where

import qualified Control.Monad.Catch as Exceptions
import Control.Monad.Reader (
    ReaderT (ReaderT),
    runReaderT,
 )
import Data.Int (
    Int64,
 )
import Database.SQLite.Simple (
    FromRow,
    NamedParam,
    Query,
    SQLData (..),
 )
import qualified Database.SQLite.Simple as SQLite
import Prelude.Kore

-- | @SQL@ is a 'Monad' for executing SQL statements.
newtype SQL a = SQL {getSQL :: ReaderT SQLite.Connection IO a}
    deriving newtype (Functor, Applicative, Monad)
    deriving newtype (MonadIO)

instance (Semigroup a) => Semigroup (SQL a) where
    (<>) sqlt1 sqlt2 = SQL $ (<>) <$> getSQL sqlt1 <*> getSQL sqlt2

instance (Monoid a) => Monoid (SQL a) where
    mempty = pure mempty

-- | Run the given sequence of statements in the named database.
runSQL ::
    -- | SQLite database
    FilePath ->
    -- | statements
    SQL a ->
    IO a
runSQL filePath =
    Exceptions.bracket
        (liftIO $ SQLite.open filePath)
        (liftIO . SQLite.close)
        . runReaderT
        . getSQL

execute_ :: Query -> SQL ()
execute_ q = SQL . ReaderT $ \conn -> SQLite.execute_ conn q

execute :: Query -> [SQLData] -> SQL ()
execute q values = SQL . ReaderT $ \conn -> SQLite.execute conn q values

executeNamed :: Query -> [NamedParam] -> SQL ()
executeNamed q params =
    SQL . ReaderT $ \conn -> SQLite.executeNamed conn q params

lastInsertRowId :: SQL Int64
lastInsertRowId = SQL . ReaderT $ SQLite.lastInsertRowId

queryNamed :: FromRow r => Query -> [NamedParam] -> SQL [r]
queryNamed q params =
    SQL . ReaderT $ \conn -> SQLite.queryNamed conn q params

query :: FromRow r => Query -> [SQLData] -> SQL [r]
query q params =
    SQL . ReaderT $ \conn -> SQLite.query conn q params
