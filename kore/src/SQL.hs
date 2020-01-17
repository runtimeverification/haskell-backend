{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module SQL
    ( tableNameSOP
    , createTableNP
    , createTableGeneric
    , createTableWrapper
    , createTableUnwrapped
    , insertRowNP
    , insertRowGeneric
    , insertRowWrapper
    , insertRowUnwrapped
    , selectRowNP
    , selectRowGeneric
    , selectRowWrapper
    , selectRowUnwrapped
    -- * Re-exports
    , module SQL.Table
    ) where

import qualified Control.Lens as Lens
import Data.Generics.Wrapped
import Data.Proxy
    ( Proxy (..)
    )
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import qualified Database.SQLite.Simple as SQLite
import Generics.SOP
    ( I (..)
    , K (..)
    , NP (..)
    , NS (..)
    , Shape (..)
    )
import qualified Generics.SOP as SOP

import SQL.Table

createTableNP
    :: forall xs
    .  SOP.All Column xs
    => SQLite.Connection
    -> TableName
    -> NP SOP.FieldInfo xs
    -> IO ()
createTableNP conn tableName fields =
    createTableAux conn tableName =<< sequence columns
  where
    columns :: [IO (Text, ColumnDef)]
    columns = SOP.hcollapse (SOP.hcmap (Proxy @Column) column fields)
    column :: Column a => SOP.FieldInfo a -> K (IO (Text, ColumnDef)) a
    column fieldInfo = K $ do
        colDef <- defineColumn conn fieldInfo
        return (fieldName fieldInfo, colDef)
    fieldName = Text.pack . SOP.fieldName

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
    createTableNP conn (tableNameSOP proxy) (productFields proxy')
  where
    proxy' = Proxy @x

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
    createTableNP conn (tableNameSOP proxy) (productFields proxy)

tableNameSOP :: SOP.HasDatatypeInfo table => proxy table -> TableName
tableNameSOP proxy =
    TableName $ SOP.moduleName info <> "." <> SOP.datatypeName info
  where
    info = SOP.datatypeInfo proxy

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

insertRowNP
    :: forall table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => TableName
    -> SQLite.Connection
    -> table
    -> IO (Key table)
insertRowNP tableName conn table = do
    columns <- productColumns conn table
    SQL.Table.insertRowAux conn tableName columns

insertRowGeneric
    :: forall table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => SQLite.Connection
    -> table
    -> IO (Key table)
insertRowGeneric =
    insertRowNP (tableNameSOP proxy)
  where
    proxy = Proxy @table

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
    <$> insertRowNP (tableNameSOP proxy) conn (Lens.view iso table)
  where
    proxy = pure @Proxy table

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

productTypeFrom
    :: forall a xs
    .  (SOP.Code a ~ '[xs], SOP.IsProductType a xs)
    => a -> NP I xs
productTypeFrom a =
    case ns of
        Z np -> np
        S _  -> error "impossible"
  where
    ns :: NS (NP I) '[xs]
    SOP.SOP ns = SOP.from a

productColumns
    :: forall table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => SQLite.Connection
    -> table
    -> IO [(String, SQLite.SQLData)]
productColumns conn table =
    sequence (SOP.hcollapse columns)
  where
    proxy = pure @SOP.Proxy table
    fields = productFields proxy
    values = productTypeFrom table
    columns = SOP.hczipWith (Proxy @Column) column fields values
    column
        :: Column a
        => SOP.FieldInfo a
        -> I a
        -> K (IO (String, SQLite.SQLData)) a
    column info (I x) = K $ do
        x' <- toColumn conn x
        return (SOP.fieldName info, x')

selectRowNP
    :: forall table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => SQLite.Connection
    -> TableName
    -> table
    -> IO (Maybe (Key table))
selectRowNP conn tableName table = do
    columns <- productColumns conn table
    selectRowAux conn tableName columns

selectRowGeneric
    :: forall table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => SQLite.Connection
    -> table
    -> IO (Maybe (Key table))
selectRowGeneric conn table =
    selectRowNP conn (tableNameSOP proxy) table
  where
    proxy = pure @SOP.Proxy table

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
    <$> selectRowNP conn (tableNameSOP proxy) (Lens.view iso table)
  where
    proxy = pure @Proxy table

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
