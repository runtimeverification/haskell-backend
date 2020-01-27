{-|
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module SQL.Table
    ( defineForeignKeyColumn
    , toForeignKeyColumn
    , Table (..)
    , insertUniqueRow
    -- * Re-exports
    , SQLite.Connection
    , Proxy (..)
    , module SQL.Column
    , module SQL.Key
    ) where

import qualified Control.Monad.Extra as Monad
import Data.Int
    ( Int64
    )
import Data.Proxy
    ( Proxy (..)
    )
import Data.Typeable
    ( Typeable
    )
import qualified Database.SQLite.Simple as SQLite

import SQL.Column
    ( Column (..)
    , ColumnConstraint
    , ColumnDef (..)
    , TypeName
    , defineTextColumn
    )
import SQL.Key
import qualified SQL.SOP as SOP
import SQL.SQL as SQL

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

To derive an instance for your type,

@
-- Note: All fields must have a 'Column' instance.
data DataType = ...
    deriving ('GHC.Generics.Generic', 'Data.Typeable.Typeable')

instance 'Generics.SOP.Generic' DataType

instance 'Generics.SOP.HasDatatypeInfo' DataType

instance Table DataType

-- Recommended: Add a foreign key 'Column' instance if other tables
-- might refer to DataType.
instance 'Column' DataType where
    defineColumn = 'defineForeignKeyColumn'
    toColumn = 'toForeignKeyColumn'
@

 -}
class Typeable a => Table a where
    -- | Create the table for @a@ if it does not exist.
    createTable :: proxy a -> SQL ()
    default createTable
        :: SOP.HasDatatypeInfo a
        => SOP.All2 Column (SOP.Code a)
        => proxy a
        -> SQL ()
    createTable = SOP.createTableGeneric

    {- | Insert the @a@ as a new row in the table.

    Returns the 'Key' of the inserted row.

     -}
    insertRow :: a -> SQL (Key a)
    default insertRow
        :: SOP.HasDatatypeInfo a
        => SOP.All2 Column (SOP.Code a)
        => a
        -> SQL (Key a)
    insertRow = SOP.insertRowGeneric

    {- | Find the 'Key' for an @a@, if it is in the table.
     -}
    selectRow :: a -> SQL (Maybe (Key a))
    default selectRow
        :: SOP.HasDatatypeInfo a
        => SOP.All2 Column (SOP.Code a)
        => a
        -> SQL (Maybe (Key a))
    selectRow = SOP.selectRowGeneric

instance Table ()

instance (Column a, Typeable a) => Table (Maybe a)

instance (Column a, Typeable a, Column b, Typeable b) => Table (Either a b)

{- | @(insertUniqueRow a)@ inserts @a@ into the table if not present.

Returns the 'Key' of the row corresponding to @a@.

 -}
insertUniqueRow :: Table a => a -> SQL (Key a)
insertUniqueRow a = Monad.maybeM (insertRow a) return (selectRow a)
