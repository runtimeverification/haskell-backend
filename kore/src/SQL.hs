{-# OPTIONS_GHC -fno-warn-redundant-constraints #-}

module SQL
    ( Key (..)
    , defineForeignKeyColumn
    , toForeignKeyColumn
    , Table (..)
    , insertUniqueRow
    , TableName (..)
    , createTableAux
    , createTableNP
    , insertRowAux
    , insertRowNP
    , selectRowAux
    , selectRowNP
    -- * Re-exports
    , SQLite.Connection
    , module SQL.Column
    ) where

import qualified Control.Monad.Extra as Monad
import qualified Data.Bifunctor as Bifunctor
import Data.Int
    ( Int64
    )
import Data.Proxy
import qualified Data.Set as Set
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
    ( Column (..)
    , ColumnConstraint
    , ColumnDef (..)
    , TypeName
    , defineTextColumn
    )
import qualified SQL.Column as Column

newtype Key a = Key { getKey :: Int64 }

instance Column (Key a) where
    defineColumn conn _ = defineColumn conn (Proxy @Int64)
    toColumn conn = toColumn conn . getKey

defineForeignKeyColumn
    :: Table a => SQLite.Connection -> proxy a -> IO ColumnDef
defineForeignKeyColumn conn proxy = do
    createTable conn proxy
    defineColumn conn (Proxy @Int64)

toForeignKeyColumn :: Table a => SQLite.Connection -> a -> IO SQLite.SQLData
toForeignKeyColumn conn a =
    insertUniqueRow conn a >>= toColumn conn

class Table a where
    createTable :: SQLite.Connection -> proxy a -> IO ()

    insertRow :: SQLite.Connection -> a -> IO (Key a)

    selectRow :: SQLite.Connection -> a -> IO (Maybe (Key a))

insertUniqueRow :: Table a => SQLite.Connection -> a -> IO (Key a)
insertUniqueRow conn a =
    Monad.maybeM (insertRow conn a) return (selectRow conn a)

newtype TableName = TableName { getTableName :: String }

createTableAux :: SQLite.Connection -> TableName -> [(Text, ColumnDef)] -> IO ()
createTableAux conn tableName fields = do
    SQLite.execute_ conn $ SQLite.Query $ Text.unwords
        [ "CREATE TABLE IF NOT EXISTS"
        , (quotes . Text.pack) (getTableName tableName)
        , parens (sepBy ", " columns)
        ]
  where
    quotes str = Text.cons '"' (Text.snoc str '"')
    parens str = Text.cons '(' (Text.snoc str ')')
    sepBy _   [      ] = Text.empty
    sepBy _   [x     ] = x
    sepBy sep (x : xs) = x <> sep <> sepBy sep xs
    idField =
        ("id", ColumnDef { columnType, columnConstraints })
      where
        columnType = Column.typeInteger
        columnConstraints = Column.primaryKey
    columns = column <$> (idField : fields)
    column (columnName, ColumnDef { columnType, columnConstraints }) =
        Text.unwords
            ( columnName
            : Column.getTypeName columnType
            : map Column.getColumnConstraint (Set.toList columnConstraints)
            )

createTableNP
    :: forall proxy table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => SQLite.Connection
    -> proxy table
    -> IO ()
createTableNP conn proxy = do
    createTableAux conn tableName =<< sequence columns
  where
    tableName = tableNameSOP proxy

    fields = productFields proxy
    columns :: [IO (Text, ColumnDef)]
    columns = SOP.hcollapse (SOP.hcmap (Proxy @Column) column fields)
    column :: Column a => SOP.FieldInfo a -> K (IO (Text, ColumnDef)) a
    column fieldInfo = K $ do
        colDef <- defineColumn conn fieldInfo
        return (fieldName fieldInfo, colDef)
    fieldName = Text.pack . SOP.fieldName

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

insertRowAux
    :: SQLite.Connection
    -> TableName
    -> [(String, SQLite.SQLData)]
    -> IO (Key a)
insertRowAux conn tableName fields = do
    let query =
            (SQLite.Query . Text.unwords)
                [ "INSERT INTO"
                , (quotes . Text.pack) (getTableName tableName)
                , "VALUES"
                , parens (sepBy ", " names)
                ]
    SQLite.executeNamed conn query (map (uncurry (SQLite.:=)) params)
    SQL.Key <$> SQLite.lastInsertRowId conn
  where
    quotes str = Text.cons '"' (Text.snoc str '"')
    parens str = Text.cons '(' (Text.snoc str ')')
    sepBy _   [      ] = Text.empty
    sepBy _   [x     ] = x
    sepBy sep (x : xs) = x <> sep <> sepBy sep xs
    names = fst <$> params
    params = map (Bifunctor.first $ Text.pack . (:) ':') fields'
    fields' = ("id", SQLite.SQLNull) : fields

insertRowNP
    :: forall table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => SQLite.Connection
    -> table
    -> IO (Key table)
insertRowNP conn table = do
    columns <- productColumns conn table
    insertRowAux conn tableName columns
  where
    proxy = pure @SOP.Proxy table
    tableName = tableNameSOP proxy

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

selectRowAux
    :: SQLite.Connection
    -> TableName
    -> [(String, SQLite.SQLData)]
    -> IO (Maybe (Key a))
selectRowAux conn tableName fields = do
    let query =
            (SQLite.Query . Text.unwords)
                [ "SELECT (id) FROM"
                , (quotes . Text.pack) (getTableName tableName)
                , "WHERE"
                , sepBy " AND " exprs
                ]
    ids <- SQLite.queryNamed conn query params
    case SQLite.fromOnly <$> ids of
        getKey : _ -> (return . Just) SQL.Key { getKey }
        [] -> return Nothing
  where
    quotes str = Text.cons '"' (Text.snoc str '"')
    sepBy _   [      ] = Text.empty
    sepBy _   [x     ] = x
    sepBy sep (x : xs) = x <> sep <> sepBy sep xs
    exprs = map expr fields
    expr (columnName, _) =
        Text.unwords [ Text.pack columnName, "IS", paramName columnName ]
    params = map (namedParam . Bifunctor.first paramName) fields
    namedParam = uncurry (SQLite.:=)
    paramName = Text.pack . (:) ':'

selectRowNP
    :: forall table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => SQLite.Connection
    -> table
    -> IO (Maybe (Key table))
selectRowNP conn table = do
    columns <- productColumns conn table
    selectRowAux conn tableName columns
  where
    proxy = pure @SOP.Proxy table
    tableName = tableNameSOP proxy
