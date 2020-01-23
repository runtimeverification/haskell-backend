{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module SQL.SQL
    ( SQL (..)
    , runSQL
    , execute_
    , executeNamed
    , queryNamed
    , lastInsertRowId
    ) where

import qualified Control.Monad.Catch as Exceptions
import Control.Monad.IO.Class
    ( MonadIO
    , liftIO
    )
import Control.Monad.Reader
    ( ReaderT (ReaderT)
    , runReaderT
    )
import Data.Int
    ( Int64
    )
import Database.SQLite.Simple
    ( FromRow
    , NamedParam
    , Query
    )
import qualified Database.SQLite.Simple as SQLite

newtype SQL a = SQL { getSQL :: ReaderT SQLite.Connection IO a }
    deriving (Functor, Applicative, Monad)
    deriving (MonadIO)

instance (Semigroup a) => Semigroup (SQL a) where
    (<>) sqlt1 sqlt2 = SQL $ (<>) <$> getSQL sqlt1 <*> getSQL sqlt2

instance (Monoid a) => Monoid (SQL a) where
    mempty = pure mempty

runSQL :: FilePath -> SQL a -> IO a
runSQL filePath =
    Exceptions.bracket
        (liftIO $ SQLite.open filePath)
        (liftIO . SQLite.close)
    . runReaderT
    . getSQL

execute_ :: Query -> SQL ()
execute_ query = SQL . ReaderT $ \conn -> SQLite.execute_ conn query

executeNamed :: Query -> [NamedParam] -> SQL ()
executeNamed query params =
    SQL . ReaderT $ \conn -> SQLite.executeNamed conn query params

lastInsertRowId :: SQL Int64
lastInsertRowId = SQL . ReaderT $ SQLite.lastInsertRowId

queryNamed :: FromRow r => Query -> [NamedParam] -> SQL [r]
queryNamed query params =
    SQL . ReaderT $ \conn -> SQLite.queryNamed conn query params
