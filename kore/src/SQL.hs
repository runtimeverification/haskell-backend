module SQL
    ( Key (..)
    , Table (..)
    , TableName (..)
    , createTableAux
    -- * Re-exports
    , SQLite.Connection
    , module SQL.Column
    ) where

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
