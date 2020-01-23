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
    -- * Re-exports
    , SQLite.Connection
    , Proxy (..)
    , module SQL.Column
    ) where

import qualified Control.Monad.Extra as Monad
import Data.Int
    ( Int64
    )
import Data.Proxy
    ( Proxy (..)
    )
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
import SQL.SQL as SQL

{- | A foreign key into the table for type @a@.
 -}
newtype Key a = Key { getKey :: Int64 }
    deriving (Eq, Ord, Read, Show)
    deriving (Functor, Foldable)
    deriving (GHC.Generic)

instance SOP.Generic (Key a)

instance SOP.HasDatatypeInfo (Key a)

instance Debug (Key a)

instance Diff (Key a)

instance Column (Key a) where
    defineColumn _ = defineColumn (Proxy @Int64)
    toColumn = toColumn . getKey

{- | Implement 'defineColumn' for a foreign key reference.

The referenced table will be created if it does not exist.

 -}
defineForeignKeyColumn :: Table a => proxy a -> SQL ColumnDef
defineForeignKeyColumn proxy = do
    createTable proxy
    defineColumn (Proxy @Int64)

{- | Implement 'toColumn' for a foreign key reference.

Inserts the given data into the table and returns a key to the inserted row.

 -}
toForeignKeyColumn :: Table table => table -> SQL SQLite.SQLData
toForeignKeyColumn a = insertUniqueRow a >>= toColumn

{- | A 'Table' corresponds to a table in SQL.
 -}
class Table a where
    -- | Create the table for @a@ if it does not exist.
    createTable :: proxy a -> SQL ()

    {- | Insert the @a@ as a new row in the table.

    Returns the 'Key' of the inserted row.

     -}
    insertRow :: a -> SQL (Key a)

    {- | Find the 'Key' for an @a@, if it is in the table.
     -}
    selectRow :: a -> SQL (Maybe (Key a))

{- | @(insertUniqueRow a)@ inserts @a@ into the table if not present.

Returns the 'Key' of the row corresponding to @a@.

 -}
insertUniqueRow :: Table a => a -> SQL (Key a)
insertUniqueRow a = Monad.maybeM (insertRow a) return (selectRow a)

newtype TableName = TableName { getTableName :: String }
