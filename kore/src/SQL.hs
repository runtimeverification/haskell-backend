{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module SQL
    (
    -- * Generic table types
      createTableGeneric
    , insertRowGeneric
    , selectRowGeneric
    -- * Table isomorphisms
    , createTableIso
    , insertRowIso
    , selectRowIso
    -- * Table newtypes
    , createTableUnwrapped
    , insertRowUnwrapped
    , selectRowUnwrapped
    -- * Re-exports
    , module SQL.SQL
    , module SQL.Table
    ) where

import qualified Control.Lens as Lens
import Data.Generics.Wrapped
import Data.Proxy
    ( Proxy (..)
    )
import qualified Generics.SOP as SOP

import qualified SQL.SOP
import SQL.SQL
import SQL.Table

createTableIso
    :: forall proxy outer inner fields
    .  SOP.HasDatatypeInfo outer
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => SOP.All Column fields
    => Lens.Iso' outer inner
    -> proxy outer
    -> SQL ()
createTableIso _ proxy =
    SQL.SOP.createTable tableName fields
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
    => proxy outer
    -> SQL ()
createTableUnwrapped = createTableIso _Unwrapped

createTableGeneric
    :: forall proxy table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
    => proxy table
    -> SQL ()
createTableGeneric proxy =
    SQL.SOP.createTable tableName fields
  where
    tableName = SQL.SOP.tableNameGeneric proxy
    fields = SQL.SOP.productFields proxy

insertRowGeneric
    :: forall table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
    => table
    -> SQL (Key table)
insertRowGeneric =
    SQL.SOP.insertRow tableName
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @table)

insertRowIso
    :: forall outer inner fields
    .  SOP.HasDatatypeInfo outer
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => SOP.All Column fields
    => Lens.Iso' outer inner
    -> outer
    -> SQL (Key outer)
insertRowIso iso table =
    fmap (Lens.review iso)
    <$> SQL.SOP.insertRow tableName (Lens.view iso table)
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @outer)

insertRowUnwrapped
    :: forall outer inner fields
    .  (SOP.HasDatatypeInfo outer)
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => SOP.All Column fields
    => Wrapped outer outer inner inner
    => outer
    -> SQL (Key outer)
insertRowUnwrapped = insertRowIso _Unwrapped

selectRowGeneric
    :: forall table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
    => table
    -> SQL (Maybe (Key table))
selectRowGeneric table =
    SQL.SOP.selectRow tableName table
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @table)

selectRowIso
    :: forall outer inner fields
    .  (SOP.HasDatatypeInfo outer)
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => SOP.All Column fields
    => Lens.Iso' outer inner
    -> outer
    -> SQL (Maybe (Key outer))
selectRowIso iso table =
    (fmap . fmap) (Lens.review iso)
    <$> SQL.SOP.selectRow tableName (Lens.view iso table)
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @outer)

selectRowUnwrapped
    :: forall outer inner fields
    .  SOP.HasDatatypeInfo outer
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => SOP.All Column fields
    => Wrapped outer outer inner inner
    => outer
    -> SQL (Maybe (Key outer))
selectRowUnwrapped = selectRowIso _Unwrapped
