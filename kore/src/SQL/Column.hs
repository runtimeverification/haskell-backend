module SQL.Column
    ( TypeName
    , getTypeName
    , typeInteger
    , typeText
    , ColumnConstraint
    , getColumnConstraint
    , notNull
    , primaryKey
    , ColumnDef (..)
    , Column (..)
    ) where

import Data.Int
    ( Int64
    )
import Data.Proxy
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import qualified Database.SQLite.Simple as SQLite

newtype TypeName = TypeName { getTypeName :: Text }
    deriving (Eq, Ord, Read, Show)

typeInteger :: TypeName
typeInteger = TypeName "INTEGER"

typeText :: TypeName
typeText = TypeName "TEXT"

newtype ColumnConstraint = ColumnConstraint { getColumnConstraint :: Text }
    deriving (Eq, Ord, Read, Show)

notNull :: Set ColumnConstraint
notNull = Set.singleton (ColumnConstraint "NOT NULL")

primaryKey :: Set ColumnConstraint
primaryKey = Set.singleton (ColumnConstraint "PRIMARY KEY")

newtype ColumnDef =
    ColumnDef { getColumnDef :: (TypeName, Set ColumnConstraint) }

class Column a where
    columnDef :: proxy a -> ColumnDef
    fromColumn :: SQLite.Connection -> SQLite.SQLData -> IO a
    toColumn :: SQLite.Connection -> a -> IO SQLite.SQLData

instance Column Int64 where
    columnDef _ = ColumnDef (typeInteger, notNull)
    toColumn _ = return . SQLite.SQLInteger
    fromColumn _ = withInteger . withJust $ return

instance Column Text where
    columnDef _ = ColumnDef (typeText, notNull)
    toColumn _ = return . SQLite.SQLText
    fromColumn _ = withText . withJust $ return

instance Column a => Column (Maybe a) where
    columnDef _ =
        ColumnDef (type', Set.difference constraints notNull)
      where
        ColumnDef (type', constraints) = columnDef (Proxy @a)
    toColumn conn = maybe (return SQLite.SQLNull) (toColumn conn)
    fromColumn conn =
        \case
            SQLite.SQLNull -> return Nothing
            sqlData        -> Just <$> fromColumn conn sqlData

withInteger :: (Maybe Int64 -> IO a) -> SQLite.SQLData -> IO a
withInteger continue =
    \case
        SQLite.SQLInteger int64 -> continue (Just int64)
        SQLite.SQLNull          -> continue  Nothing
        sqlData                 -> typeError "INTEGER" (typeOf sqlData)

withText :: (Maybe Text -> IO a) -> SQLite.SQLData -> IO a
withText continue =
    \case
        SQLite.SQLText text -> continue (Just text)
        SQLite.SQLNull      -> continue  Nothing
        sqlData             -> typeError "TEXT" (typeOf sqlData)

typeOf :: SQLite.SQLData -> Text
typeOf (SQLite.SQLInteger _) = "INTEGER"
typeOf (SQLite.SQLFloat   _) = "FLOAT"
typeOf (SQLite.SQLText    _) = "TEXT"
typeOf (SQLite.SQLBlob    _) = "BLOB"
typeOf (SQLite.SQLNull     ) = "NULL"

typeError :: Text -> Text -> a
typeError expected actual =
    (error . Text.unpack . Text.unwords)
        [ "type error:"
        , "expected"
        , expected
        , "but found"
        , actual
        ]

withJust :: (a -> IO b) -> Maybe a -> IO b
withJust continue = maybe (typeError "NOT NULL" "NULL") continue
