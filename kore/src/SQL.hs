{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module SQL
    ( createTableGeneric
    , insertRowGeneric
    , selectRowGeneric
    , createTableWrapper
    , insertRowWrapper
    , selectRowWrapper
    , createTableUnwrapped
    , insertRowUnwrapped
    , selectRowUnwrapped
    -- * Re-exports
    , module SQL.Table
    ) where

import qualified Control.Lens as Lens
import Data.Generics.Wrapped
import Data.Proxy
    ( Proxy (..)
    )
import qualified Database.SQLite.Simple as SQLite
import qualified Generics.SOP as SOP

import qualified SQL.SOP
import SQL.Table

createTableWrapper
    :: forall proxy outer inner fields
    .  SOP.HasDatatypeInfo outer
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => SOP.All Column fields
    => Lens.Iso' outer inner
    -> SQLite.Connection
    -> proxy outer
    -> IO ()
createTableWrapper _ conn proxy =
    SQL.SOP.createTable conn tableName fields
  where
    proxy' = Proxy @inner
    tableName = SQL.SOP.tableNameGeneric proxy
    fields = SQL.SOP.productFields proxy'

createTableUnwrapped
    :: forall proxy outer inner fields
    .  SOP.HasDatatypeInfo outer
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => SOP.All Column fields
    => Wrapped outer outer inner inner
    => SQLite.Connection
    -> proxy outer
    -> IO ()
createTableUnwrapped = createTableWrapper _Unwrapped

createTableGeneric
    :: forall proxy table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
    => SQLite.Connection
    -> proxy table
    -> IO ()
createTableGeneric conn proxy =
    SQL.SOP.createTable conn tableName fields
  where
    tableName = SQL.SOP.tableNameGeneric proxy
    fields = SQL.SOP.productFields proxy

insertRowGeneric
    :: forall table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
    => SQLite.Connection
    -> table
    -> IO (Key table)
insertRowGeneric =
    SQL.SOP.insertRow tableName
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @table)

insertRowWrapper
    :: forall outer inner fields
    .  SOP.HasDatatypeInfo outer
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => SOP.All Column fields
    => Lens.Iso' outer inner
    -> SQLite.Connection
    -> outer
    -> IO (Key outer)
insertRowWrapper iso conn table =
    fmap (Lens.review iso)
    <$> SQL.SOP.insertRow tableName conn (Lens.view iso table)
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @outer)

insertRowUnwrapped
    :: forall s a fields
    .  (SOP.HasDatatypeInfo s)
    => (SOP.HasDatatypeInfo a, SOP.IsProductType a fields)
    => SOP.All Column fields
    => Wrapped s s a a
    => SQLite.Connection
    -> s
    -> IO (Key s)
insertRowUnwrapped = insertRowWrapper _Unwrapped

selectRowGeneric
    :: forall table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
    => SQLite.Connection
    -> table
    -> IO (Maybe (Key table))
selectRowGeneric conn table =
    SQL.SOP.selectRow conn tableName table
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @table)

selectRowWrapper
    :: forall outer inner fields
    .  (SOP.HasDatatypeInfo outer)
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => SOP.All Column fields
    => Lens.Iso' outer inner
    -> SQLite.Connection
    -> outer
    -> IO (Maybe (Key outer))
selectRowWrapper iso conn table =
    (fmap . fmap) (Lens.review iso)
    <$> SQL.SOP.selectRow conn tableName (Lens.view iso table)
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @outer)

selectRowUnwrapped
    :: forall outer inner fields
    .  SOP.HasDatatypeInfo outer
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => SOP.All Column fields
    => Wrapped outer outer inner inner
    => SQLite.Connection
    -> outer
    -> IO (Maybe (Key outer))
selectRowUnwrapped = selectRowWrapper _Unwrapped
