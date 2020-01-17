{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module SQL.SQL
    ( SQLT (..)
    , runSQLT
    , SQL
    , runSQL
    , execute_
    , executeNamed
    , queryNamed
    , lastInsertRowId
    ) where

import Control.Monad.Catch
    ( MonadMask
    )
import qualified Control.Monad.Catch as Exceptions
import Control.Monad.IO.Class
    ( MonadIO
    , liftIO
    )
import Control.Monad.Morph
    ( MFunctor
    , MMonad
    )
import Control.Monad.Reader
    ( ReaderT (ReaderT)
    , runReaderT
    )
import Control.Monad.Trans.Class
    ( MonadTrans
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

newtype SQLT monad a = SQLT { getSQLT :: ReaderT SQLite.Connection monad a }
    deriving (Functor, Applicative, Monad)
    deriving (MonadTrans, MonadIO, MFunctor, MMonad)

instance (Applicative functor, Semigroup a) => Semigroup (SQLT functor a) where
    (<>) sqlt1 sqlt2 = SQLT $ (<>) <$> getSQLT sqlt1 <*> getSQLT sqlt2

instance (Applicative functor, Monoid a) => Monoid (SQLT functor a) where
    mempty = pure mempty

runSQLT
    :: (MonadIO monad, MonadMask monad)
    => FilePath
    -> SQLT monad a
    -> monad a
runSQLT filePath sqlt =
    Exceptions.bracket
        (liftIO $ SQLite.open filePath)
        (liftIO . SQLite.close)
        (runReaderT (getSQLT sqlt))

type SQL = SQLT IO

runSQL :: FilePath -> SQL a -> IO a
runSQL = runSQLT

execute_ :: Query -> SQL ()
execute_ query = SQLT . ReaderT $ \conn -> SQLite.execute_ conn query

executeNamed :: Query -> [NamedParam] -> SQL ()
executeNamed query params =
    SQLT . ReaderT $ \conn -> SQLite.executeNamed conn query params

lastInsertRowId :: SQL Int64
lastInsertRowId = SQLT . ReaderT $ SQLite.lastInsertRowId

queryNamed :: FromRow r => Query -> [NamedParam] -> SQL [r]
queryNamed query params =
    SQLT . ReaderT $ \conn -> SQLite.queryNamed conn query params
