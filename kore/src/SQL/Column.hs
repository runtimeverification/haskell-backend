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
    toColumn :: SQLite.Connection -> a -> IO SQLite.SQLData
    -- TODO (thomas.tuegel): Implement this!
    -- fromColumn :: SQLite.Connection -> SQLite.SQLData -> IO a

instance Column Int64 where
    columnDef _ = ColumnDef (typeInteger, notNull)
    toColumn _ = return . SQLite.SQLInteger

instance Column Text where
    columnDef _ = ColumnDef (typeText, notNull)
    toColumn _ = return . SQLite.SQLText

instance Column a => Column (Maybe a) where
    columnDef _ =
        ColumnDef (type', Set.difference constraints notNull)
      where
        ColumnDef (type', constraints) = columnDef (Proxy @a)
    toColumn conn = maybe (return SQLite.SQLNull) (toColumn conn)
