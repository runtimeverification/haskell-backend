{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

'Table' definitions for 'SOP.Generic' types.

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
import SQL.SQL
import SQL.Table hiding
    ( createTable
    , insertRow
    , selectRow
    )

{- | Create a table with the given name and columns.

The columns are described as record fields.

 -}
createTable
    :: forall fields
    .  SOP.All Column fields
    => TableName
    -> NP SOP.FieldInfo fields
    -> SQL ()
createTable tableName fields =
    createTableAux tableName =<< sequence columns
  where
    columns :: [SQL (Text, ColumnDef)]
    columns = SOP.hcollapse (SOP.hcmap (Proxy @Column) column fields)
    column :: Column a => SOP.FieldInfo a -> K (SQL (Text, ColumnDef)) a
    column fieldInfo = K $ do
        colDef <- defineColumn fieldInfo
        return (fieldName fieldInfo, colDef)
    fieldName = Text.pack . SOP.fieldName

{- | The 'TableName' of a 'SOP.Generic' type.
 -}
tableNameGeneric :: SOP.HasDatatypeInfo table => proxy table -> TableName
tableNameGeneric proxy =
    TableName $ SOP.moduleName info <> "." <> SOP.datatypeName info
  where
    info = SOP.datatypeInfo proxy

{- | The record fields of a product type.

If the type is not actually a record (if it hase a regular or infix
constructor), then suitable field names are invented to be used as SQL column
names.

 -}
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
    -> table
    -> SQL (Key table)
insertRow tableName table = do
    columns <- productColumns table
    SQL.Table.insertRowAux tableName columns

{- | Witness that the type @table@ is actually a product type.
 -}
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

{- | The field values of a product type.

 -}
productColumns
    :: forall table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
    => table
    -> SQL [(String, SQLite.SQLData)]
productColumns table =
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
        -> K (SQL (String, SQLite.SQLData)) a
    column info (I x) = K $ do
        x' <- toColumn x
        return (SOP.fieldName info, x')

selectRow
    :: forall table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
    => TableName
    -> table
    -> SQL (Maybe (Key table))
selectRow tableName table = do
    columns <- productColumns table
    selectRowAux tableName columns
