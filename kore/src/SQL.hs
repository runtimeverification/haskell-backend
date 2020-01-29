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
    , module SQL.Column
    , module SQL.SQL
    , module SQL.Table
    ) where

import Prelude.Kore

import qualified Control.Lens as Lens
import Data.Generics.Wrapped
import Data.Proxy
    ( Proxy (..)
    )
import Data.Typeable
    ( Typeable
    )
import qualified Generics.SOP as SOP

import SQL.Column
import SQL.SOP as SOP
import SQL.SQL
import SQL.Table

{- | @(createTableIso iso)@ implements 'createTable'.

The table will be named for the @outer@ type (see 'createTableGeneric'). The
'Iso' determines the structure of the table: the table will have the same
columns as the table that 'createTableGeneric' would create for the @inner@
type. Note, however, that the @inner@ type need not have a 'Table' instance!

 -}
createTableIso
    :: forall proxy outer inner
    .  Typeable outer
    => (SOP.HasDatatypeInfo inner, SOP.All2 Column (SOP.Code inner))
    => Lens.Iso' outer inner
    -> proxy outer
    -> SQL ()
createTableIso _ proxy =
    createTableGenericAux tableName proxy'
  where
    proxy' = Proxy @inner
    tableName = SOP.tableNameTypeable proxy

{- | @(insertRowIso iso)@ implements 'insertRow' for a table created with
'createTableIso'.
 -}
insertRowIso
    :: forall outer inner
    .  Typeable outer
    => (SOP.HasDatatypeInfo inner, SOP.All2 Column (SOP.Code inner))
    => Lens.Iso' outer inner
    -> outer
    -> SQL (Key outer)
insertRowIso iso outer =
    fromInnerKey <$> insertRowGenericAux tableName inner
  where
    tableName = SOP.tableNameTypeable (Proxy @outer)
    inner = Lens.view iso outer
    fromInnerKey :: Key inner -> Key outer
    fromInnerKey = fmap (Lens.review iso)

{- | @(selectRowIso iso)@ implements 'selectRow' for a table created with
'createTableIso'.
 -}
selectRowIso
    :: forall outer inner
    .  Typeable outer
    => (SOP.HasDatatypeInfo inner, SOP.All2 Column (SOP.Code inner))
    => Lens.Iso' outer inner
    -> outer
    -> SQL (Maybe (Key outer))
selectRowIso iso outer =
    fromInnerKeys <$> selectRowGenericAux tableName inner
  where
    tableName = SOP.tableNameTypeable (Proxy @outer)
    inner = Lens.view iso outer
    fromInnerKeys :: Maybe (Key inner) -> Maybe (Key outer)
    fromInnerKeys = (fmap . fmap) (Lens.review iso)

{- | @createTableUnwrapped@ implements 'createTable' for a @newtype@ wrapper.

The table will be named for the @outer@ type (see 'createTableGeneric'), but it
will have the same columns as the table that 'createTableGeneric' would create
for the @inner@ type. Note, however, that the @inner@ type need not have a
'Table' instance!

See also: 'createTableIso' is a more general version of this function.

 -}
createTableUnwrapped
    :: forall proxy outer inner
    .  Typeable outer
    => SOP.HasDatatypeInfo inner
    => SOP.All2 Column (SOP.Code inner)
    => Wrapped outer outer inner inner
    => proxy outer
    -> SQL ()
createTableUnwrapped = createTableIso _Unwrapped

{- | @insertRowUnwrapped@ implements 'insertRow' for a @newtype@ wrapper.
 -}
insertRowUnwrapped
    :: forall outer inner
    .  Typeable outer
    => SOP.HasDatatypeInfo inner
    => SOP.All2 Column (SOP.Code inner)
    => Wrapped outer outer inner inner
    => outer
    -> SQL (Key outer)
insertRowUnwrapped = insertRowIso _Unwrapped

{- | @selectRowUnwrapped@ implements 'selectRow' for a @newtype@ wrapper.
 -}
selectRowUnwrapped
    :: forall outer inner
    .  Typeable outer
    => SOP.HasDatatypeInfo inner
    => SOP.All2 Column (SOP.Code inner)
    => Wrapped outer outer inner inner
    => outer
    -> SQL (Maybe (Key outer))
selectRowUnwrapped = selectRowIso _Unwrapped
