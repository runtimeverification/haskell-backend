{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module SQL.SOP
    ( tableNameGeneric
    , createTable
    , insertRow
    , selectRow
    -- * Re-exports
    , module SQL.Table
    ) where

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

import SQL.Column
import SQL.Table hiding
    ( createTable
    , insertRow
    , selectRow
    )

createTable
    :: forall xs
    .  SOP.All Column xs
    => SQLite.Connection
    -> TableName
    -> NP SOP.FieldInfo xs
    -> IO ()
createTable conn tableName fields =
    createTableAux conn tableName =<< sequence columns
  where
    columns :: [IO (Text, ColumnDef)]
    columns = SOP.hcollapse (SOP.hcmap (Proxy @Column) column fields)
    column :: Column a => SOP.FieldInfo a -> K (IO (Text, ColumnDef)) a
    column fieldInfo = K $ do
        colDef <- defineColumn conn fieldInfo
        return (fieldName fieldInfo, colDef)
    fieldName = Text.pack . SOP.fieldName

tableNameGeneric :: SOP.HasDatatypeInfo table => proxy table -> TableName
tableNameGeneric proxy =
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

insertRow
    :: forall table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => TableName
    -> SQLite.Connection
    -> table
    -> IO (Key table)
insertRow tableName conn table = do
    columns <- productColumns conn table
    SQL.Table.insertRowAux conn tableName columns

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

selectRow
    :: forall table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => SQLite.Connection
    -> TableName
    -> table
    -> IO (Maybe (Key table))
selectRow conn tableName table = do
    columns <- productColumns conn table
    selectRowAux conn tableName columns
