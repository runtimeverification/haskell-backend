{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

'Table' definitions for 'SOP.Generic' types.

-}

{-# LANGUAGE PolyKinds #-}

module SQL.SOP
    ( TableName
    , tableNameGeneric
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
    ( ConstructorInfo
    , I (..)
    , K (..)
    , NP (..)
    , NS (..)
    , Shape (..)
    )
import qualified Generics.SOP as SOP

import SQL.Column as Column
import SQL.Key as Key
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
    stmt <- flip execAccumT mempty $ do
        Accum.add "CREATE TABLE IF NOT EXISTS"
        addSpace
        addTableName tableName
        addSpace
        addColumnDefs names defs
    SQL.execute_ stmt

addSpace :: Monad m => AccumT Query m ()
addSpace = Accum.add " "

addComma :: Monad m => AccumT Query m ()
addComma = Accum.add ", "

addColumnDefs
    :: SOP.All SOP.Top fields
    => NP (K String) fields
    -> NP (K ColumnDef) fields
    -> AccumT Query SQL ()
addColumnDefs names defs = parenthesized $ defineFields names defs

defineFields
    :: SOP.All SOP.Top fields
    => NP (K String) fields
    -> NP (K ColumnDef) fields
    -> AccumT Query SQL ()
defineFields Nil               _ = Accum.add "id INTEGER PRIMARY KEY"
defineFields (name :* names) (def :* defs) = do
    defineField name def
    addComma
    defineFields names defs

defineField :: K String field -> K ColumnDef field -> AccumT Query SQL ()
defineField name (K defined) = do
    addColumnName name
    addSpace
    let ColumnDef { columnType } = defined
    Accum.add $ fromString $ Column.getTypeName columnType
    let ColumnDef { columnConstraints } = defined
    Foldable.for_ columnConstraints $ \constraint -> do
        addSpace
        Accum.add $ fromString $ Column.getColumnConstraint constraint

defineColumns
    :: SOP.All Column fields
    => NP f fields
    -> SQL (NP (K ColumnDef) fields)
defineColumns =
    SOP.hctraverse' (Proxy @Column) $ \proxy -> K <$> defineColumn proxy

{- | The 'TableName' of a 'SOP.Generic' type.
 -}
tableNameGeneric :: SOP.HasDatatypeInfo table => proxy table -> TableName
tableNameGeneric proxy =
    TableName $ SOP.moduleName info <> "." <> SOP.datatypeName info
  where
    info = SOP.datatypeInfo proxy

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
    .  SOP.HasDatatypeInfo table
    => SOP.All2 Column (SOP.Code table)
    => proxy table
    -> SQL ()
createTableGeneric proxy =
    createTableGenericAux tableName proxy
  where
    tableName = tableNameGeneric proxy

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
    .  SOP.All SOP.Top fields
    => TableName
    -> NP (K String) fields
    -> NP (K SQLData) fields
    -> SQL (Key table)
insertRow tableName infos values = do
    stmt <- flip execAccumT mempty $ do
        Accum.add "INSERT INTO"
        addSpace
        addTableSpec tableName infos'
        addSpace
        Accum.add "VALUES"
        addSpace
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
    .  SOP.HasDatatypeInfo table
    => SOP.All2 Column (SOP.Code table)
    => table
    -> SQL (Key table)
insertRowGeneric =
    insertRowGenericAux tableName
  where
    proxy = Proxy @table
    tableName = tableNameGeneric proxy

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
    stmt <- flip execAccumT mempty $ do
        Accum.add "SELECT (id) FROM"
        addSpace
        addTableName tableName
        addSpace
        Monad.unless (isNil infos) $ do
            Accum.add "WHERE"
            addSpace
            addColumnNames infos
            Accum.add " = "
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
    .  SOP.HasDatatypeInfo table
    => SOP.All2 Column (SOP.Code table)
    => table
    -> SQL (Maybe (Key table))
selectRowGeneric = selectRowGenericAux tableName
  where
    proxy = Proxy @table
    tableName = tableNameGeneric proxy

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
