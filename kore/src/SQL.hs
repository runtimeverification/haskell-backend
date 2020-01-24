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
import Generics.SOP
    ( FieldInfo
    , I
    , NP
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

withIsoFields
    :: forall outer inner fields a
    .  SOP.HasDatatypeInfo outer
    => (SOP.HasDatatypeInfo inner, SOP.IsProductType inner fields)
    => (TableName -> NP FieldInfo fields -> NP I fields -> SQL a)
    -> Lens.Iso' outer inner
    -> outer
    -> SQL a
withIsoFields continue iso outer =
    continue tableName infos fields
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @outer)
    inner = Lens.view iso outer
    infos = SQL.SOP.productFields (Proxy @inner)
    fields = SQL.SOP.productTypeFrom inner

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
insertRowIso iso outer =
    fromInnerKey <$> withIsoFields SQL.SOP.insertRow iso outer
  where
    fromInnerKey :: Key inner -> Key outer
    fromInnerKey = fmap (Lens.review iso)

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
selectRowIso iso outer = do
    keys <- fromInnerKeys <$> withIsoFields SQL.SOP.selectRows iso outer
    return $ case keys of
        []      -> Nothing
        key : _ -> Just key
  where
    fromInnerKeys :: [Key inner] -> [Key outer]
    fromInnerKeys = (fmap . fmap) (Lens.review iso)

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

withGenericFields
    :: forall table fields a
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => (TableName -> NP FieldInfo fields -> NP I fields -> SQL a)
    -> table
    -> SQL a
withGenericFields continue table =
    continue tableName infos fields
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @table)
    infos = SQL.SOP.productFields (Proxy @table)
    fields = SQL.SOP.productTypeFrom table

{- | @insertRowGeneric@ implements 'insertRow' for a 'SOP.Generic' record type.
 -}
insertRowGeneric
    :: forall table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
    => table
    -> SQL (Key table)
insertRowGeneric = withGenericFields SQL.SOP.insertRow

{- | @selectRowGeneric@ implements 'selectRow' for a 'SOP.Generic' record type.
 -}
selectRowGeneric
    :: forall table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
    => table
    -> SQL (Maybe (Key table))
selectRowGeneric table = do
    keys <- withGenericFields SQL.SOP.selectRows table
    return $ case keys of
        []      -> Nothing
        key : _ -> Just key
