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
import Generics.SOP
    ( NP (..)
    , Shape (..)
    )
import qualified Generics.SOP as SOP

import qualified SQL.SOP
import SQL.Table

createTableWrapper
    :: forall proxy new x xs
    .  SOP.HasDatatypeInfo new
    => (SOP.HasDatatypeInfo x, SOP.IsProductType x xs)
    => SOP.All Column xs
    => Lens.Iso' new x
    -> SQLite.Connection
    -> proxy new
    -> IO ()
createTableWrapper _ conn proxy =
    SQL.SOP.createTable conn tableName (productFields proxy')
  where
    proxy' = Proxy @x
    tableName = SQL.SOP.tableNameGeneric proxy

createTableUnwrapped
    :: forall proxy s a xs
    .  SOP.HasDatatypeInfo s
    => (SOP.HasDatatypeInfo a, SOP.IsProductType a xs)
    => SOP.All Column xs
    => Wrapped s s a a
    => SQLite.Connection
    -> proxy s
    -> IO ()
createTableUnwrapped = createTableWrapper _Unwrapped

createTableGeneric
    :: forall proxy table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => SQLite.Connection
    -> proxy table
    -> IO ()
createTableGeneric conn proxy =
    SQL.SOP.createTable conn tableName (productFields proxy)
  where
    tableName = SQL.SOP.tableNameGeneric proxy

productFields
    :: forall proxy a xs
    .  (SOP.HasDatatypeInfo a, SOP.IsProductType a xs)
    => proxy a
    -> NP SOP.FieldInfo xs
productFields proxy =
    case ctor of
        SOP.Constructor _ -> fakeFields
        SOP.Infix _ _ _ -> fakeFields
        SOP.Record _ fieldsNP -> fieldsNP
  where
    info = SOP.datatypeInfo proxy
    ctor :* Nil = SOP.constructorInfo info

    fakeFields :: forall ys. SOP.SListI ys => NP SOP.FieldInfo ys
    fakeFields = shapeFields 0 SOP.shape

    shapeFields :: forall ys. Int -> Shape ys -> NP SOP.FieldInfo ys
    shapeFields _  ShapeNil         = Nil
    shapeFields n (ShapeCons shape) =
        SOP.FieldInfo ("field" <> show n) :* shapeFields (n + 1) shape

insertRowGeneric
    :: forall table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => SQLite.Connection
    -> table
    -> IO (Key table)
insertRowGeneric =
    SQL.SOP.insertRow tableName
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @table)

insertRowWrapper
    :: forall new x xs
    .  (SOP.HasDatatypeInfo new)
    => (SOP.HasDatatypeInfo x, SOP.IsProductType x xs)
    => SOP.All Column xs
    => Lens.Iso' new x
    -> SQLite.Connection
    -> new
    -> IO (Key new)
insertRowWrapper iso conn table =
    fmap (Lens.review iso)
    <$> SQL.SOP.insertRow tableName conn (Lens.view iso table)
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @new)

insertRowUnwrapped
    :: forall s a xs
    .  (SOP.HasDatatypeInfo s)
    => (SOP.HasDatatypeInfo a, SOP.IsProductType a xs)
    => SOP.All Column xs
    => Wrapped s s a a
    => SQLite.Connection
    -> s
    -> IO (Key s)
insertRowUnwrapped = insertRowWrapper _Unwrapped

selectRowGeneric
    :: forall table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => SQLite.Connection
    -> table
    -> IO (Maybe (Key table))
selectRowGeneric conn table =
    SQL.SOP.selectRow conn tableName table
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @table)

selectRowWrapper
    :: forall new x xs
    .  (SOP.HasDatatypeInfo new)
    => (SOP.HasDatatypeInfo x, SOP.IsProductType x xs)
    => SOP.All Column xs
    => Lens.Iso' new x
    -> SQLite.Connection
    -> new
    -> IO (Maybe (Key new))
selectRowWrapper iso conn table =
    (fmap . fmap) (Lens.review iso)
    <$> SQL.SOP.selectRow conn tableName (Lens.view iso table)
  where
    tableName = SQL.SOP.tableNameGeneric (Proxy @new)

selectRowUnwrapped
    :: forall s a xs
    .  SOP.HasDatatypeInfo s
    => (SOP.HasDatatypeInfo a, SOP.IsProductType a xs)
    => SOP.All Column xs
    => Wrapped s s a a
    => SQLite.Connection
    -> s
    -> IO (Maybe (Key s))
selectRowUnwrapped = selectRowWrapper _Unwrapped
