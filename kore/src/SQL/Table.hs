{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module SQL.Table
    ( Key (..)
    , defineForeignKeyColumn
    , toForeignKeyColumn
    , Table (..)
    , insertUniqueRow
    , TableName (..)
    , createTableAux
    , insertRowAux
    , selectRowAux
    -- * Re-exports
    , SQLite.Connection
    , Proxy (..)
    , module SQL.Column
    ) where

import qualified Control.Monad.Extra as Monad
import qualified Data.Bifunctor as Bifunctor
import Data.Int
    ( Int64
    )
import Data.Proxy
    ( Proxy (..)
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import qualified Database.SQLite.Simple as SQLite
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Debug
import SQL.Column
    ( Column (..)
    , ColumnConstraint
    , ColumnDef (..)
    , TypeName
    , defineTextColumn
    )
import qualified SQL.Column as Column

newtype Key a = Key { getKey :: Int64 }
    deriving (Eq, Ord, Read, Show)
    deriving (Functor, Foldable)
    deriving (GHC.Generic)

instance SOP.Generic (Key a)

instance SOP.HasDatatypeInfo (Key a)

instance Debug (Key a)

instance Diff (Key a)

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
createTableAux conn tableName fields =
    SQLite.execute_ conn $ SQLite.Query $ Text.unwords
        [ "CREATE TABLE IF NOT EXISTS"
        , (quotes . Text.pack) (getTableName tableName)
        , parens (sepBy ", " columns)
        ]
  where
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
    Key <$> SQLite.lastInsertRowId conn
  where
    names = fst <$> params
    params = map (Bifunctor.first $ Text.pack . (:) ':') fields'
    fields' = ("id", SQLite.SQLNull) : fields

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
        getKey : _ -> (return . Just) Key { getKey }
        [] -> return Nothing
  where
    exprs = map expr fields
    expr (columnName, _) =
        Text.unwords [ Text.pack columnName, "IS", paramName columnName ]
    params = map (namedParam . Bifunctor.first paramName) fields
    namedParam = uncurry (SQLite.:=)
    paramName = Text.pack . (:) ':'

quotes :: Text -> Text
quotes str = Text.cons '"' (Text.snoc str '"')

sepBy :: Text -> [Text] -> Text
sepBy _   [      ] = Text.empty
sepBy _   [x     ] = x
sepBy sep (x : xs) = x <> sep <> sepBy sep xs

parens :: Text -> Text
parens str = Text.cons '(' (Text.snoc str ')')
