{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module SQL.SOP
    ( tableNameGeneric
    , createTable
    , insertRow
    , selectRow
    , productFields
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
    :: forall fields
    .  SOP.All Column fields
    => SQLite.Connection
    -> TableName
    -> NP SOP.FieldInfo fields
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
    :: forall proxy table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => proxy table
    -> NP SOP.FieldInfo fields
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
    :: forall table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
    => TableName
    -> SQLite.Connection
    -> table
    -> IO (Key table)
insertRow tableName conn table = do
    columns <- productColumns conn table
    SQL.Table.insertRowAux conn tableName columns

productTypeFrom
    :: forall table fields
    .  SOP.IsProductType table fields
    => table -> NP I fields
productTypeFrom a =
    case ns of
        Z np -> np
        S _  -> error "impossible"
  where
    ns :: NS (NP I) '[fields]
    SOP.SOP ns = SOP.from a

productColumns
    :: forall table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
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
    :: forall table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
    => SQLite.Connection
    -> TableName
    -> table
    -> IO (Maybe (Key table))
selectRow conn tableName table = do
    columns <- productColumns conn table
    selectRowAux conn tableName columns
