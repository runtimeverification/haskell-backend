{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

'Table' definitions for 'SOP.Generic' types.

-}

{-# LANGUAGE PolyKinds #-}

module SQL.SOP
    ( TableName
    , tableNameTypeable
    -- * Low-level building blocks
    , createTable
    , insertRow
    , selectRows
    -- * Sum types
    , createTableSum
    , insertRowSum
    , selectRowsSum
    -- * Product types
    , createTableProduct
    , insertRowProduct
    , selectRowsProduct
    -- * Generic implementations
    , createTableGeneric, createTableGenericAux
    , insertRowGeneric, insertRowGenericAux
    , selectRowGeneric, selectRowGenericAux
    -- * Helpers
    , defineColumns
    , productFields
    , ctorFields
    , productTypeFrom
    , toColumns
    -- * Re-exports
    , SOP.HasDatatypeInfo
    , SOP.All2
    , SOP.Code
    ) where

import qualified Control.Monad as Monad
import qualified Data.Foldable as Foldable
import Data.Proxy
    ( Proxy (..)
    )
import Data.Typeable
    ( Typeable
    )
import qualified Database.SQLite.Simple as SQLite
import Generics.SOP
    ( ConstructorInfo
    , I (..)
    , K (..)
    , NP (..)
    , NS (..)
    , Shape (..)
    )
import qualified Generics.SOP as SOP
import Type.Reflection
    ( someTypeRep
    )

import SQL.Column as Column
import SQL.Key as Key
import SQL.Query
    ( AccumT
    , Query
    )
import qualified SQL.Query as Query
import SQL.SQL as SQL

newtype TableName = TableName { getTableName :: String }

{- | Create a table with the given name and columns.

The columns are described as record fields.

 -}
createTable
    :: forall fields
    .  SOP.All SOP.Top fields
    => TableName
    -> NP (K String) fields  -- ^ column names
    -> NP (K ColumnDef) fields  -- ^ column definitions
    -> SQL ()
createTable tableName names defs = do
    stmt <- Query.build $ do
        Query.add "CREATE TABLE IF NOT EXISTS"
        Query.addSpace
        addTableName tableName
        Query.addSpace
        addColumnDefs names defs
    SQL.execute_ stmt

addColumnDefs
    :: SOP.All SOP.Top fields
    => NP (K String) fields
    -> NP (K ColumnDef) fields
    -> AccumT Query SQL ()
addColumnDefs names defs = Query.withParens $ defineFields names defs

defineFields
    :: SOP.All SOP.Top fields
    => NP (K String) fields
    -> NP (K ColumnDef) fields
    -> AccumT Query SQL ()
defineFields Nil               _ = Query.add "id INTEGER PRIMARY KEY"
defineFields (name :* names) (def :* defs) = do
    defineField name def
    Query.addComma
    defineFields names defs

defineField :: K String field -> K ColumnDef field -> AccumT Query SQL ()
defineField name (K defined) = do
    addColumnName name
    Query.addSpace
    let ColumnDef { columnType } = defined
    Query.addString $ Column.getTypeName columnType
    let ColumnDef { columnConstraints } = defined
    Foldable.for_ columnConstraints $ \constraint -> do
        Query.addSpace
        Query.addString $ Column.getColumnConstraint constraint

defineColumns
    :: SOP.All Column fields
    => NP f fields
    -> SQL (NP (K ColumnDef) fields)
defineColumns =
    SOP.hctraverse' (Proxy @Column) $ \proxy -> K <$> defineColumn proxy

{- | The 'TableName' of a 'Typeable' type.
 -}
tableNameTypeable :: Typeable table => proxy table -> TableName
tableNameTypeable proxy = TableName (show $ someTypeRep proxy)

{- | @createTableProduct@ implements 'createTable' for a product type.
 -}
createTableProduct
    :: forall fields
    .  SOP.All Column fields
    => TableName
    -> ConstructorInfo fields
    -> SQL ()
createTableProduct tableName ctorInfo = do
    defs <- defineColumns names
    createTable tableName names defs
  where
    names = ctorFields ctorInfo

createTableSum
    :: forall ctors
    .  SOP.All2 Column ctors
    => TableName
    -> NP ConstructorInfo ctors
    -> SQL ()
createTableSum tableName ctors = do
    SOP.hctraverse_ proxyAllColumn (createConstructorTable tableName) ctors
    createTable tableName names defs
  where
    proxyAllColumn = Proxy @(SOP.All Column)

    names :: NP (K String) ctors
    names = columnNamesSum ctors

    defs :: NP (K ColumnDef) ctors
    defs = SOP.hmap (const $ K columnTag) names

{- | @createTableGeneric@ implements 'createTable' for a 'SOP.Generic' type.
 -}
createTableGeneric
    :: forall proxy table
    .  Typeable table
    => (SOP.HasDatatypeInfo table, SOP.All2 Column (SOP.Code table))
    => proxy table
    -> SQL ()
createTableGeneric proxy = createTableGenericAux (tableNameTypeable proxy) proxy

createTableGenericAux
    :: forall proxy table
    .  SOP.HasDatatypeInfo table
    => SOP.All2 Column (SOP.Code table)
    => TableName
    -> proxy table
    -> SQL ()
createTableGenericAux tableName proxy =
    case SOP.constructorInfo $ SOP.datatypeInfo proxy of
        info :* Nil -> createTableProduct tableName info
        infos       -> createTableSum     tableName infos

columnTag :: ColumnDef
columnTag = Column.columnDef Column.typeInteger

tagColumnName :: ConstructorInfo fields -> String
tagColumnName info = "tag_" <> SOP.constructorName info

columnNamesSum
    :: SOP.All SOP.Top ctors
    => NP ConstructorInfo ctors
    -> NP (K String) ctors
columnNamesSum = SOP.hmap (K . tagColumnName)

createConstructorTable
    :: forall fields
    .  SOP.All Column fields
    => TableName
    -> ConstructorInfo fields
    -> SQL ()
createConstructorTable typeTableName info = do
    defs <- SQL.SOP.defineColumns names
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
productFields
    :: forall proxy table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => proxy table
    -> NP (K String) fields
productFields proxy =
    ctorFields ctor
  where
    info = SOP.datatypeInfo proxy
    ctor :* Nil = SOP.constructorInfo info

ctorFields
    :: SOP.All SOP.Top fields
    => ConstructorInfo fields
    -> NP (K String) fields
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
    shapeFields _  ShapeNil         = Nil
    shapeFields n (ShapeCons shape) =
        K ("field" <> show n) :* shapeFields (n + 1) shape

addTableName :: Monad m => TableName -> AccumT Query m ()
addTableName tableName =
    Query.withDoubleQuotes . Query.addString $ getTableName tableName

insertRow
    :: forall table fields
    .  SOP.All SOP.Top fields
    => TableName
    -> NP (K String) fields
    -> NP (K SQLData) fields
    -> SQL (Key table)
insertRow tableName infos values = do
    stmt <- Query.build $ do
        Query.add "INSERT INTO"
        Query.addSpace
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

addTableSpec
    :: Monad m
    => TableName
    -> NP (K String) fields
    -> AccumT Query m ()
addTableSpec tableName infos = do
    addTableName tableName
    Query.addSpace
    addColumnNames infos

addColumnNames
    :: forall fields m
    .  Monad m
    => NP (K String) fields
    -> AccumT Query m ()
addColumnNames =
    Query.withParens . worker
  where
    worker :: forall fields'. NP (K String) fields' -> AccumT Query m ()
    worker Nil = return ()
    worker (info :* infos) = do
        addColumnName info
        case infos of
            Nil -> return ()
            _   -> Query.addComma >> worker infos

addColumnName :: Monad m => K String field -> AccumT Query m ()
addColumnName (K fieldName) = Query.addString fieldName

addColumnParams
    :: forall f fields m
    .  Monad m
    => NP f fields
    -> AccumT Query m ()
addColumnParams =
    Query.withParens . worker
  where
    worker :: forall fields'. NP f fields' -> AccumT Query m ()
    worker Nil = return ()
    worker (_ :* infos) = do
        Query.add "?"
        case infos of
            Nil -> return ()
            _   -> Query.addComma >> worker infos

toColumns :: SOP.All Column fields => NP I fields -> SQL (NP (K SQLData) fields)
toColumns = SOP.hctraverse' (Proxy @Column) $ \(I field) -> K <$> toColumn field

insertRowSum
    :: forall table ctors
    .  SOP.All2 Column ctors
    => TableName
    -> NP ConstructorInfo ctors
    -> NS (NP I) ctors
    -> SQL (Key table)
insertRowSum typeTableName = worker
  where
    worker
        :: forall ctors'
        .  SOP.All2 Column ctors'
        => NP ConstructorInfo ctors'
        -> NS (NP I) ctors'
        -> SQL (Key table)
    worker infos (S ctors) =
        case infos of
            _ :* infos' -> worker infos' ctors
    worker (info :* _) (Z fields) = do
        key <- insertIndexRow
        let names = K "id" :* K tagName :* ctorFields info
            rowid = SQLInteger (getKey key)
        values <- toColumns fields
        insertRow tableName names (K rowid :* K tag :* values)
      where
        tableName = ctorTableName typeTableName info
        tagName = tagColumnName info
        tag = SQLInteger 1

        insertIndexRow = do
            let names = K tagName :* Nil
                values = K tag :* Nil
            insertRow typeTableName names values

{- | @insertRowProduct@ implements 'insertRow' for a product type.
 -}
insertRowProduct
    :: forall table fields
    .  (SOP.HasDatatypeInfo table, SOP.Code table ~ '[fields])
    => SOP.All Column fields
    => TableName
    -> SOP.ConstructorInfo fields
    -> NP I fields
    -> SQL (Key table)
insertRowProduct tableName ctorInfo fields = do
    values <- toColumns fields
    insertRow tableName infos values
  where
    infos = ctorFields ctorInfo

{- | @insertRowGeneric@ implements 'insertRow' for a 'SOP.Generic' record type.
 -}
insertRowGeneric
    :: forall table
    .  Typeable table
    => (SOP.HasDatatypeInfo table, SOP.All2 Column (SOP.Code table))
    => table
    -> SQL (Key table)
insertRowGeneric = insertRowGenericAux (tableNameTypeable (Proxy @table))

insertRowGenericAux
    :: forall table
    .  SOP.HasDatatypeInfo table
    => SOP.All2 Column (SOP.Code table)
    => TableName
    -> table
    -> SQL (Key table)
insertRowGenericAux tableName table = do
    case SOP.constructorInfo $ SOP.datatypeInfo proxy of
        info :* Nil ->
            case ctors of
                S ctors' -> case ctors' of {}
                Z fields -> insertRowProduct tableName info fields
        infos       -> insertRowSum tableName infos ctors
  where
    proxy = Proxy @table
    ctors = SOP.unSOP $ SOP.from table

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

isNil :: NP f xs -> Bool
isNil Nil = True
isNil _   = False

selectRows
    :: forall table fields
    .  SOP.All Column fields
    => TableName
    -> NP (K String) fields
    -> NP (K SQLData) fields
    -> SQL [Key table]
selectRows tableName infos values = do
    stmt <- Query.build $ do
        Query.add "SELECT (id) FROM"
        Query.addSpace
        addTableName tableName
        Query.addSpace
        Monad.unless (isNil infos) $ do
            Query.add "WHERE"
            Query.addSpace
            addColumnNames infos
            Query.add " = "
            addColumnParams infos
    keys <- SQL.query stmt $ SOP.hcollapse values
    return (Key . SQLite.fromOnly <$> keys)

selectRowsSum
    :: forall table ctors
    .  SOP.All2 Column ctors
    => TableName
    -> NP ConstructorInfo ctors
    -> NS (NP I) ctors
    -> SQL [Key table]
selectRowsSum typeTableName = worker
  where
    worker
        :: forall ctors'
        .  SOP.All2 Column ctors'
        => NP ConstructorInfo ctors'
        -> NS (NP I) ctors'
        -> SQL [Key table]
    worker infos (S ctors) =
        case infos of
            _ :* infos' -> worker infos' ctors
    worker (info :* _) (Z fields) = do
        let names = ctorFields info
        values <- toColumns fields
        selectRows tableName names values
      where
        tableName = ctorTableName typeTableName info

{- | @selectRowsProduct@ implements 'selectRow' for a product type
 -}
selectRowsProduct
    :: forall table fields
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table fields)
    => SOP.All Column fields
    => TableName
    -> ConstructorInfo fields
    -> NP I fields
    -> SQL [Key table]
selectRowsProduct tableName ctorInfo fields = do
    values <- toColumns fields
    selectRows tableName infos values
  where
    infos = ctorFields ctorInfo

{- | @selectRowGeneric@ implements 'selectRow' for a 'SOP.Generic' record type.
 -}
selectRowGeneric
    :: forall table
    .  Typeable table
    => (SOP.HasDatatypeInfo table, SOP.All2 Column (SOP.Code table))
    => table
    -> SQL (Maybe (Key table))
selectRowGeneric = selectRowGenericAux (tableNameTypeable (Proxy @table))

selectRowGenericAux
    :: forall table
    .  SOP.HasDatatypeInfo table
    => SOP.All2 Column (SOP.Code table)
    => TableName
    -> table
    -> SQL (Maybe (Key table))
selectRowGenericAux tableName table = do
    keys <- case SOP.constructorInfo $ SOP.datatypeInfo proxy of
        info :* Nil ->
            case ctors of
                S ctors' -> case ctors' of {}
                Z fields -> selectRowsProduct tableName info fields
        infos -> selectRowsSum tableName infos ctors
    return $ case keys of
        []      -> Nothing
        key : _ -> Just key
  where
    proxy = Proxy @table
    ctors = SOP.unSOP $ SOP.from table
