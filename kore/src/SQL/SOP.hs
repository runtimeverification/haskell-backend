{-# LANGUAGE PolyKinds #-}

{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause

'Table' definitions for 'SOP.Generic' types.
-}
module SQL.SOP (
    -- * Columns
    ColumnImpl (..),

    -- * Tables
    TableName (..),
    tableNameTypeable,

    -- * Low-level building blocks
    createTable,
    insertRow,
    selectRows,

    -- * Sum types
    createTableSum,
    insertRowSum,
    selectRowsSum,

    -- * Product types
    createTableProduct,
    insertRowProduct,
    selectRowsProduct,

    -- * Generic implementations
    createTableGenericAux,
    insertRowGenericAux,
    selectRowGenericAux,

    -- * Helpers
    defineColumns,
    productFields,
    ctorFields,
    productTypeFrom,
    toColumns,

    -- * Re-exports
    SOP.HasDatatypeInfo,
    SOP.All2,
    SOP.Code,
) where

import Data.Functor.Product
import Data.Proxy (
    Proxy (..),
 )
import qualified Database.SQLite.Simple as SQLite
import Generics.SOP (
    ConstructorInfo,
    I (..),
    K (..),
    NP (..),
    NS (..),
    Shape (..),
 )
import qualified Generics.SOP as SOP
import Prelude.Kore
import SQL.ColumnDef as Column
import SQL.Key as Key
import SQL.Query (
    AccumT,
 )
import qualified SQL.Query as Query
import SQL.SQL as SQL
import Type.Reflection (
    someTypeRep,
 )

{- | @ColumnImpl@ is a concrete implementation of the 'SQL.Column' typeclass.

By separating the concrete implementation from the constraint, we can decouple
this module from the class declaration.
-}
data ColumnImpl a = ColumnImpl
    { defineColumnImpl :: forall proxy. TableName -> proxy a -> SQL ColumnDef
    , toColumnImpl :: a -> SQL SQLite.SQLData
    }

newtype TableName = TableName {getTableName :: String}
    deriving stock (Eq, Ord)

-- | The 'TableName' of a 'Typeable' type.
tableNameTypeable :: Typeable table => proxy table -> TableName
tableNameTypeable proxy = TableName (show $ someTypeRep proxy)

{- | Create a table with the given name and columns.

The columns are described as record fields. An extra column named @id@ is added
to hold the primary key.
-}
createTable ::
    forall fields.
    SOP.All SOP.Top fields =>
    TableName ->
    -- | column names
    NP (K String) fields ->
    -- | column definitions
    NP (K ColumnDef) fields ->
    SQL ()
createTable tableName names defs = do
    stmt <- Query.build $ do
        Query.add "CREATE TABLE IF NOT EXISTS"
        addTableName tableName
        addColumnDefs names defs
    SQL.execute_ stmt

-- | Insert a row into the named table.
insertRow ::
    forall table fields.
    SOP.All SOP.Top fields =>
    TableName ->
    -- | column names
    NP (K String) fields ->
    -- | row data
    NP (K SQLData) fields ->
    SQL (Key table)
insertRow tableName infos values = do
    stmt <- Query.build $ do
        Query.add "INSERT INTO"
        addTableSpec tableName infos'
        Query.addSpace
        Query.add "VALUES"
        Query.addSpace
        addColumnParams infos'
    SQL.execute stmt $ SOP.hcollapse values'
    Key <$> SQL.lastInsertRowId
  where
    infos' = K "id" :* infos
    values' = K SQLNull :* values

-- | Select all rows that match the provided row.
selectRows ::
    forall table fields.
    SOP.All SOP.Top fields =>
    TableName ->
    -- | column names
    NP (K String) fields ->
    -- | row data
    NP (K SQLData) fields ->
    SQL [Key table]
selectRows tableName infos values = do
    stmt <- Query.build $ do
        Query.add "SELECT (id) FROM"
        addTableName tableName
        Query.addSpace
        unless (isNil infos) $ do
            Query.add "WHERE"
            Query.addSpace
            addColumnNames infos
            Query.add " = "
            addColumnParams infos
    keys <- SQL.query stmt $ SOP.hcollapse values
    return (Key . SQLite.fromOnly <$> keys)

{- | Add column definitions to a @CREATE TABLE@ statement.

The column definitions look like:

@
(text TEXT NOT NULL, id INTEGER PRIMARY KEY)
@

The @id@ field is automatically added to the provided list of columns.
-}
addColumnDefs ::
    SOP.All SOP.Top fields =>
    -- | column names
    NP (K String) fields ->
    -- | column definitions
    NP (K ColumnDef) fields ->
    AccumT Query SQL ()
addColumnDefs names defs = do
    Query.addSpace
    Query.withParens $ do
        let columns = SOP.hzipWith Pair names defs
        SOP.hcfor_ (Proxy @SOP.Top) columns $ \column -> do
            let Pair name (K defined) = column
            addColumnName name
            Query.addSpace
            let ColumnDef{columnType} = defined
            addColumnType columnType
            let ColumnDef{columnConstraints} = defined
            for_ columnConstraints $ \constraint -> do
                Query.addSpace
                addColumnConstraint constraint
            Query.addComma
        Query.add "id INTEGER PRIMARY KEY"

addColumnType :: Monad monad => TypeName -> AccumT Query monad ()
addColumnType = Query.addString . Column.getTypeName

addColumnConstraint :: Monad monad => ColumnConstraint -> AccumT Query monad ()
addColumnConstraint = Query.addString . Column.getColumnConstraint

defineColumns ::
    SOP.All SOP.Top fields =>
    TableName ->
    NP ColumnImpl fields ->
    SQL (NP (K ColumnDef) fields)
defineColumns tableName =
    SOP.htraverse' $ \ColumnImpl{defineColumnImpl} ->
        K <$> defineColumnImpl tableName Proxy

{- | @createTableProduct@ implements 'createTable' for a product type.

A single table is created with columns for each constructor field.
-}
createTableProduct ::
    forall fields.
    SOP.All SOP.Top fields =>
    TableName ->
    NP ColumnImpl fields ->
    ConstructorInfo fields ->
    SQL ()
createTableProduct tableName columnImpl ctorInfo = do
    defs <- defineColumns tableName columnImpl
    createTable tableName names defs
  where
    names = ctorFields ctorInfo

{- | @createTableSum@ implements 'createTable' for a sum type.

An index table is created with one "tag" column for each constructor.  A table
is created for each constructor with an extra tag column.  The index table @id@
and tag columns are used as foreign keys into the constructor tables.
-}
createTableSum ::
    forall ctors.
    SOP.All2 SOP.Top ctors =>
    TableName ->
    SOP.POP ColumnImpl ctors ->
    NP ConstructorInfo ctors ->
    SQL ()
createTableSum tableName columnImpls ctors = do
    SOP.hctraverse_
        (Proxy @(SOP.All SOP.Top))
        createTable'
        (SOP.hzipWith Pair (SOP.unPOP columnImpls) ctors)
    createTable tableName names defs
  where
    names :: NP (K String) ctors
    names = columnNamesSum ctors

    defs :: NP (K ColumnDef) ctors
    defs = SOP.hmap (const $ K columnTag) names

    createTable' ::
        forall fields.
        SOP.All SOP.Top fields =>
        Product (NP ColumnImpl) ConstructorInfo fields ->
        SQL ()
    createTable' (Pair columnImpl info) =
        createConstructorTable tableName columnImpl info

createTableGenericAux ::
    forall proxy table.
    SOP.HasDatatypeInfo table =>
    TableName ->
    SOP.POP ColumnImpl (SOP.Code table) ->
    proxy table ->
    SQL ()
createTableGenericAux tableName columnImpls proxy =
    case SOP.constructorInfo $ SOP.datatypeInfo proxy of
        info :* Nil -> createTableProduct tableName columnImpl info
          where
            columnImpl :* Nil = SOP.unPOP columnImpls
        infos -> createTableSum tableName columnImpls infos

columnTag :: ColumnDef
columnTag = Column.columnDef Column.typeInteger

tagColumnName :: ConstructorInfo fields -> String
tagColumnName info = "tag_" <> SOP.constructorName info

columnNamesSum ::
    SOP.All SOP.Top ctors =>
    NP ConstructorInfo ctors ->
    NP (K String) ctors
columnNamesSum = SOP.hmap (K . tagColumnName)

createConstructorTable ::
    forall fields.
    SOP.All SOP.Top fields =>
    TableName ->
    NP ColumnImpl fields ->
    ConstructorInfo fields ->
    SQL ()
createConstructorTable typeTableName columnImpl info = do
    defs <- defineColumns typeTableName columnImpl
    createTable tableName (K tag :* names) (K columnTag :* defs)
  where
    tag = tagColumnName info
    tableName = ctorTableName typeTableName info
    names = ctorFields info

ctorTableName :: TableName -> ConstructorInfo fields -> TableName
ctorTableName typeTableName info =
    (TableName . unwords)
        [ getTableName typeTableName
        , SOP.constructorName info
        ]

{- | The record fields of a product type.

If the type is not actually a record (if it hase a regular or infix
constructor), then suitable field names are invented to be used as SQL column
names.
-}
productFields ::
    forall proxy table fields.
    (SOP.HasDatatypeInfo table, SOP.IsProductType table fields) =>
    proxy table ->
    NP (K String) fields
productFields proxy =
    ctorFields ctor
  where
    info = SOP.datatypeInfo proxy
    ctor :* Nil = SOP.constructorInfo info

ctorFields ::
    SOP.All SOP.Top fields =>
    ConstructorInfo fields ->
    NP (K String) fields
ctorFields ctor =
    case ctor of
        SOP.Constructor _ -> fakeFields
        SOP.Infix _ _ _ -> fakeFields
        SOP.Record _ fields -> fieldNames fields
  where
    fieldNames = SOP.hmap (K . SOP.fieldName)

    fakeFields :: forall ys. SOP.SListI ys => NP (K String) ys
    fakeFields = shapeFields 0 SOP.shape

    shapeFields :: forall ys. Int -> Shape ys -> NP (K String) ys
    shapeFields _ ShapeNil = Nil
    shapeFields n (ShapeCons shape) =
        K ("field" <> show n) :* shapeFields (n + 1) shape

addTableName :: Monad m => TableName -> AccumT Query m ()
addTableName tableName = do
    Query.addSpace
    Query.withDoubleQuotes . Query.addString $ getTableName tableName

addTableSpec ::
    Monad m =>
    TableName ->
    NP (K String) fields ->
    AccumT Query m ()
addTableSpec tableName infos = do
    addTableName tableName
    Query.addSpace
    addColumnNames infos

addColumnNames ::
    forall fields m.
    Monad m =>
    NP (K String) fields ->
    AccumT Query m ()
addColumnNames =
    Query.withParens . worker
  where
    worker :: forall fields'. NP (K String) fields' -> AccumT Query m ()
    worker Nil = return ()
    worker (info :* infos) = do
        addColumnName info
        case infos of
            Nil -> return ()
            _ -> Query.addComma >> worker infos

addColumnName :: Monad m => K String field -> AccumT Query m ()
addColumnName (K fieldName) =
    Query.withDoubleQuotes . Query.addString $ fieldName

addColumnParams ::
    forall f fields m.
    Monad m =>
    NP f fields ->
    AccumT Query m ()
addColumnParams =
    Query.withParens . worker
  where
    worker :: forall fields'. NP f fields' -> AccumT Query m ()
    worker Nil = return ()
    worker (_ :* infos) = do
        Query.add "?"
        case infos of
            Nil -> return ()
            _ -> Query.addComma >> worker infos

toColumns ::
    SOP.All SOP.Top fields =>
    NP ColumnImpl fields ->
    NP I fields ->
    SQL (NP (K SQLData) fields)
toColumns columnImpls fields =
    SOP.hzipWith
        (\ColumnImpl{toColumnImpl} (I field) -> K $ toColumnImpl field)
        columnImpls
        fields
        & SOP.hsequenceK

insertRowSum ::
    forall table fields.
    SOP.All SOP.Top fields =>
    TableName ->
    NP ColumnImpl fields ->
    ConstructorInfo fields ->
    NP I fields ->
    K (SQL (Key table)) fields
insertRowSum typeTableName columnImpls info fields = K $ do
    key <- insertIndexRow
    let names = K "id" :* K tagName :* ctorFields info
        rowid = SQLInteger (getKey key)
    values <- toColumns columnImpls fields
    insertRow tableName names (K rowid :* K tag :* values)
  where
    tableName = ctorTableName typeTableName info
    tagName = tagColumnName info
    tag = SQLInteger 1

    insertIndexRow = do
        let names = K tagName :* Nil
            values = K tag :* Nil
        insertRow typeTableName names values

-- | @insertRowProduct@ implements 'insertRow' for a product type.
insertRowProduct ::
    forall table fields.
    SOP.All SOP.Top fields =>
    TableName ->
    NP ColumnImpl fields ->
    ConstructorInfo fields ->
    NP I fields ->
    K (SQL (Key table)) fields
insertRowProduct tableName columnImpl info fields = K $ do
    values <- toColumns columnImpl fields
    insertRow tableName (ctorFields info) values

insertRowGenericAux ::
    forall table.
    SOP.HasDatatypeInfo table =>
    TableName ->
    SOP.POP ColumnImpl (SOP.Code table) ->
    table ->
    SQL (Key table)
insertRowGenericAux tableName columnImpls table =
    SOP.hczipWith3 proxyAllTop insertRow' (SOP.unPOP columnImpls) ctors values
        & SOP.hcollapse
  where
    proxy = Proxy @table
    proxyAllTop = Proxy @(SOP.All SOP.Top)
    values = SOP.unSOP $ SOP.from table
    ctors = SOP.constructorInfo $ SOP.datatypeInfo proxy

    insertRow' ::
        forall fields.
        SOP.All SOP.Top fields =>
        NP ColumnImpl fields ->
        ConstructorInfo fields ->
        NP I fields ->
        K (SQL (Key table)) fields
    insertRow' =
        case ctors of
            _ :* Nil -> insertRowProduct tableName
            _ -> insertRowSum tableName

-- | Witness that the type @table@ is actually a product type.
productTypeFrom ::
    forall table fields.
    SOP.IsProductType table fields =>
    table ->
    NP I fields
productTypeFrom a =
    case ns of
        Z np -> np
        S other -> case other of
  where
    ns :: NS (NP I) '[fields]
    SOP.SOP ns = SOP.from a

isNil :: NP f xs -> Bool
isNil Nil = True
isNil _ = False

selectRowsSum ::
    forall table fields.
    SOP.All SOP.Top fields =>
    TableName ->
    NP ColumnImpl fields ->
    ConstructorInfo fields ->
    NP I fields ->
    K (SQL [Key table]) fields
selectRowsSum typeTableName columnImpl info fields = K $ do
    let names = ctorFields info
    values <- toColumns columnImpl fields
    selectRows tableName names values
  where
    tableName = ctorTableName typeTableName info

-- | @selectRowsProduct@ implements 'selectRow' for a product type
selectRowsProduct ::
    forall table fields.
    SOP.All SOP.Top fields =>
    TableName ->
    NP ColumnImpl fields ->
    ConstructorInfo fields ->
    NP I fields ->
    K (SQL [Key table]) fields
selectRowsProduct tableName columnImpl info fields = K $ do
    values <- toColumns columnImpl fields
    selectRows tableName (ctorFields info) values

selectRowGenericAux ::
    forall table.
    SOP.HasDatatypeInfo table =>
    TableName ->
    SOP.POP ColumnImpl (SOP.Code table) ->
    table ->
    SQL (Maybe (Key table))
selectRowGenericAux tableName columnImpls table = do
    keys <-
        SOP.hczipWith3
            proxyAllTop
            selectRows'
            (SOP.unPOP columnImpls)
            ctors
            values
            & SOP.hcollapse
    return $ case keys of
        [] -> Nothing
        key : _ -> Just key
  where
    proxy = Proxy @table
    proxyAllTop = Proxy @(SOP.All SOP.Top)
    ctors = SOP.constructorInfo $ SOP.datatypeInfo proxy
    values = SOP.unSOP $ SOP.from table

    selectRows' ::
        forall fields.
        SOP.All SOP.Top fields =>
        NP ColumnImpl fields ->
        ConstructorInfo fields ->
        NP I fields ->
        K (SQL [Key table]) fields
    selectRows' =
        case ctors of
            _ :* Nil -> selectRowsProduct tableName
            _ -> selectRowsSum tableName
