module SQL
    ( Key (..)
    , Table (..)
    , TableName (..)
    , createTableAux
    , createTableNP
    , insertRowAux
    -- * Re-exports
    , SQLite.Connection
    , module SQL.Column
    ) where

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
    ( K (..)
    , NP (..)
    , Shape (..)
    )
import qualified Generics.SOP as SOP

import SQL.Column
    ( Column (..)
    , ColumnConstraint
    , ColumnDef (..)
    , TypeName
    )
import qualified SQL.Column as Column

newtype Key a = Key { getKey :: Int64 }

instance Column (Key a) where
    columnDef _ = columnDef (Proxy @Int64)
    toColumn conn = toColumn conn . getKey

class Table a where
    createTable :: SQLite.Connection -> proxy a -> IO ()

    insertRow :: SQLite.Connection -> a -> IO (Key a)

    -- TODO (thomas.tuegel): Implement this!
    -- selectRow :: SQLite.Connection -> Key a -> IO a

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
    idField = ("id", ColumnDef (Column.typeInteger, Column.primaryKey))
    columns = column <$> (idField : fields)
    column (columnName, ColumnDef (typeName, columnConstraints)) =
        Text.unwords
            ( columnName
            : Column.getTypeName typeName
            : map Column.getColumnConstraint (Set.toList columnConstraints)
            )

createTableNP
    :: forall proxy table xs
    .  (SOP.HasDatatypeInfo table, SOP.IsProductType table xs)
    => SOP.All Column xs
    => SQLite.Connection
    -> proxy table
    -> IO ()
createTableNP conn proxy =
    createTableAux conn (TableName tableName) columns
  where
    info = SOP.datatypeInfo proxy
    tableName = SOP.moduleName info <> "." <> SOP.datatypeName info

    fields = productFields proxy
    columns = SOP.hcollapse (SOP.hcmap (Proxy @Column) column fields)
    column fieldInfo = K (fieldName fieldInfo, columnDef fieldInfo)
    fieldName = Text.pack . SOP.fieldName

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
    -> [(Text, SQLite.SQLData)]
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
    params = map (Bifunctor.first $ Text.cons ':') fields'
    fields' = ("id", SQLite.SQLNull) : fields
