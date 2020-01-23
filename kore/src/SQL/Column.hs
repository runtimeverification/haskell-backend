{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

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

import SQL.SQL

newtype TypeName = TypeName { getTypeName :: String }
    deriving (Eq, Ord, Read, Show)

typeInteger :: TypeName
typeInteger = TypeName "INTEGER"

typeText :: TypeName
typeText = TypeName "TEXT"

newtype ColumnConstraint = ColumnConstraint { getColumnConstraint :: String }
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

class Column a where
    defineColumn :: proxy a -> SQL ColumnDef
    toColumn :: a -> SQL SQLite.SQLData
    -- TODO (thomas.tuegel): Implement this!
    -- fromColumn :: SQLite.Connection -> SQLite.SQLData -> IO a

instance Column Int64 where
    defineColumn _ = return (columnNotNull $ columnDef typeInteger)
    toColumn = return . SQLite.SQLInteger

instance Column Text where
    defineColumn _ = return (columnNotNull $ columnDef typeText)
    toColumn = return . SQLite.SQLText

defineTextColumn :: proxy a -> SQL ColumnDef
defineTextColumn _ = defineColumn (Proxy @Text)
