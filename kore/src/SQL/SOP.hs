{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

'Table' definitions for 'SOP.Generic' types.

-}

module SQL.SOP
    ( tableNameGeneric
    , createTable
    , insertRow
    , selectRows
    , productFields
    , productTypeFrom
    -- * Re-exports
    , module SQL.Table
    ) where

import qualified Control.Monad.Trans as Trans
import Control.Monad.Trans.Accum
    ( AccumT
    , execAccumT
    )
import qualified Control.Monad.Trans.Accum as Accum
import qualified Data.Foldable as Foldable
import Data.Proxy
    ( Proxy (..)
    )
import Data.String
    ( fromString
    )
import qualified Database.SQLite.Simple as SQLite
import Generics.SOP
    ( I (..)
    , K (..)
    , NP (..)
    , NS (..)
    , Shape (..)
    )
import qualified Generics.SOP as SOP

import SQL.Column as Column
import SQL.SQL as SQL
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
    -> NP (K String) fields  -- ^ field names
    -> SQL ()
createTable tableName fields = do
    stmt <- flip execAccumT mempty $ do
        Accum.add "CREATE TABLE IF NOT EXISTS"
        addTableName tableName
        addSpace
        addColumnDefs fields
    SQL.execute_ stmt

addSpace :: Monad m => AccumT Query m ()
addSpace = Accum.add " "

addComma :: Monad m => AccumT Query m ()
addComma = Accum.add ", "

addColumnDefs
    :: SOP.All Column fields
    => NP (K String) fields
    -> AccumT Query SQL ()
addColumnDefs = parenthesized . defineFields

defineFields
    :: SOP.All Column fields
    => NP (K String) fields
    -> AccumT Query SQL ()
defineFields Nil = Accum.add "id INTEGER PRIMARY KEY"
defineFields (field :* fields) = do
    defineField field
    addComma
    defineFields fields

defineField :: Column field => K String field -> AccumT Query SQL ()
defineField field = do
    addColumnName field
    addSpace
    defined <- Trans.lift $ defineColumn field
    let ColumnDef { columnType } = defined
    Accum.add $ fromString $ Column.getTypeName columnType
    let ColumnDef { columnConstraints } = defined
    Foldable.for_ columnConstraints $ \constraint -> do
        addSpace
        Accum.add $ fromString $ Column.getColumnConstraint constraint

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
    -> NP (K String) fields
productFields proxy =
    case ctor of
        SOP.Constructor _ -> fakeFields
        SOP.Infix _ _ _ -> fakeFields
        SOP.Record _ fields -> fieldNames fields
  where
    info = SOP.datatypeInfo proxy
    ctor :* Nil = SOP.constructorInfo info

    fieldNames = SOP.hmap (K . SOP.fieldName)

    fakeFields :: forall ys. SOP.SListI ys => NP (K String) ys
    fakeFields = shapeFields 0 SOP.shape

    shapeFields :: forall ys. Int -> Shape ys -> NP (K String) ys
    shapeFields _  ShapeNil         = Nil
    shapeFields n (ShapeCons shape) =
        K ("field" <> show n) :* shapeFields (n + 1) shape

addTableName :: Monad m => TableName -> AccumT Query m ()
addTableName tableName =
    quoted $ Accum.add $ fromString $ getTableName tableName

quoted :: Monad m => AccumT Query m a -> AccumT Query m a
quoted inner = do
    Accum.add "\""
    a <- inner
    Accum.add "\""
    return a

parenthesized :: Monad m => AccumT Query m a -> AccumT Query m a
parenthesized inner = do
    Accum.add "("
    a <- inner
    Accum.add ")"
    return a

insertRow
    :: forall table fields
    .  SOP.All Column fields
    => TableName
    -> NP (K String) fields
    -> NP I fields
    -> SQL (Key table)
insertRow tableName infos fields = do
    stmt <- flip execAccumT mempty $ do
        Accum.add "INSERT INTO"
        addSpace
        addTableSpec tableName infos
        addSpace
        Accum.add "VALUES"
        addSpace
        addColumnParams infos
    values <- toColumns fields
    SQL.execute stmt values
    Key <$> SQL.lastInsertRowId

addTableSpec
    :: Monad m
    => TableName
    -> NP (K String) fields
    -> AccumT Query m ()
addTableSpec tableName infos = do
    addTableName tableName
    addSpace
    addColumnNames infos

addColumnNames
    :: forall fields m
    .  Monad m
    => NP (K String) fields
    -> AccumT Query m ()
addColumnNames =
    parenthesized . worker
  where
    worker :: forall fields'. NP (K String) fields' -> AccumT Query m ()
    worker Nil = return ()
    worker (info :* infos) = do
        addColumnName info
        case infos of
            Nil -> return ()
            _   -> addComma >> worker infos

addColumnName :: Monad m => K String field -> AccumT Query m ()
addColumnName (K fieldName) = Accum.add $ fromString fieldName

addColumnParams
    :: forall f fields m
    .  Monad m
    => NP f fields
    -> AccumT Query m ()
addColumnParams =
    parenthesized . worker
  where
    worker :: forall fields'. NP f fields' -> AccumT Query m ()
    worker Nil = return ()
    worker (_ :* infos) = do
        Accum.add "?"
        case infos of
            Nil -> return ()
            _   -> addComma >> worker infos

toColumns :: SOP.All Column fields => NP I fields -> SQL [SQLData]
toColumns Nil = return []
toColumns (I field :* fields) = do
    sqlData <- toColumn field
    (:) sqlData <$> toColumns fields

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

selectRows
    :: forall table fields
    .  SOP.All Column fields
    => TableName
    -> NP (K String) fields
    -> NP I fields
    -> SQL [Key table]
selectRows tableName infos fields = do
    stmt <- flip execAccumT mempty $ do
        Accum.add "SELECT (id) FROM"
        addSpace
        addTableName tableName
        addSpace
        Accum.add "WHERE"
        addSpace
        addColumnNames infos
        Accum.add " = "
        addColumnParams infos
    values <- toColumns fields
    keys <- SQL.query stmt values
    return (Key . SQLite.fromOnly <$> keys)
