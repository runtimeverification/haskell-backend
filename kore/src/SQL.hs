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

{- | @(createTableIso iso)@ implements 'createTable'.

The table will be named for the @outer@ type (see 'createTableGeneric'). The
'Iso' determines the structure of the table: the table will have the same
columns as the table that 'createTableGeneric' would create for the @inner@
type. Note, however, that the @inner@ type need not have a 'Table' instance!

 -}
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

{- | @(insertRowIso iso)@ implements 'insertRow' for a table created with
'createTableIso'.
 -}
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

{- | @(selectRowIso iso)@ implements 'selectRow' for a table created with
'createTableIso'.
 -}
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

{- | @createTableUnwrapped@ implements 'createTable' for a @newtype@ wrapper.

The table will be named for the @outer@ type (see 'createTableGeneric'), but it
will have the same columns as the table that 'createTableGeneric' would create
for the @inner@ type. Note, however, that the @inner@ type need not have a
'Table' instance!

See also: 'createTableIso' is a more general version of this function.

 -}
createTableUnwrapped
    :: forall proxy outer inner fields
    .  SOP.HasDatatypeInfo outer
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => SOP.All Column fields
    => Wrapped outer outer inner inner
    => proxy outer
    -> SQL ()
createTableUnwrapped = createTableIso _Unwrapped

{- | @insertRowUnwrapped@ implements 'insertRow' for a @newtype@ wrapper.
 -}
insertRowUnwrapped
    :: forall outer inner fields
    .  (SOP.HasDatatypeInfo outer)
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => SOP.All Column fields
    => Wrapped outer outer inner inner
    => outer
    -> SQL (Key outer)
insertRowUnwrapped = insertRowIso _Unwrapped

{- | @selectRowUnwrapped@ implements 'selectRow' for a @newtype@ wrapper.
 -}
selectRowUnwrapped
    :: forall outer inner fields
    .  SOP.HasDatatypeInfo outer
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => SOP.All Column fields
    => Wrapped outer outer inner inner
    => outer
    -> SQL (Maybe (Key outer))
selectRowUnwrapped = selectRowIso _Unwrapped

{- | @createTableGeneric@ implements 'createTable' for a 'SOP.Generic' record
type.
 -}
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

{- | @insertRowGeneric@ implements 'insertRow' for a 'SOP.Generic' record type.
 -}
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

{- | @selectRowGeneric@ implements 'selectRow' for a 'SOP.Generic' record type.
 -}
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
