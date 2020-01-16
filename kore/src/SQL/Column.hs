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
    , defineTextColumn
    ) where

import qualified Control.Lens as Lens
import Data.Generics.Product.Fields
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
import qualified GHC.Generics as GHC

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

data ColumnDef =
    ColumnDef
        { columnType :: !TypeName
        , columnConstraints :: !(Set ColumnConstraint)
        }
    deriving (GHC.Generic)

columnDef :: TypeName -> ColumnDef
columnDef columnType = ColumnDef { columnType, columnConstraints = mempty }

columnNotNull :: ColumnDef -> ColumnDef
columnNotNull = Lens.over (field @"columnConstraints") (<> notNull)

columnNullable :: ColumnDef -> ColumnDef
columnNullable = Lens.over (field @"columnConstraints") (Set.\\ notNull)

class Column a where
    defineColumn :: SQLite.Connection -> proxy a -> IO ColumnDef
    toColumn :: SQLite.Connection -> a -> IO SQLite.SQLData
    -- TODO (thomas.tuegel): Implement this!
    -- fromColumn :: SQLite.Connection -> SQLite.SQLData -> IO a

instance Column Int64 where
    defineColumn _ _ = return (columnNotNull $ columnDef typeInteger)
    toColumn _ = return . SQLite.SQLInteger

instance Column Text where
    defineColumn _ _ = return (columnNotNull $ columnDef typeText)
    toColumn _ = return . SQLite.SQLText

instance Column a => Column (Maybe a) where
    defineColumn conn _ = do
        colDef <- defineColumn conn (Proxy @a)
        return (columnNullable colDef)
    toColumn conn = maybe (return SQLite.SQLNull) (toColumn conn)

defineTextColumn :: SQLite.Connection -> proxy a -> IO ColumnDef
defineTextColumn conn _ = defineColumn conn (Proxy @Text)
