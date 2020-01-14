module SQL
    ( Key (..)
    , Table (..)
    -- * Re-exports
    , SQLite.Connection
    ) where

import Data.Int
    ( Int64
    )
import qualified Database.SQLite.Simple as SQLite

newtype Key a = Key { getKey :: Int64 }

class Table a where
    createTable :: SQLite.Connection -> proxy a -> IO ()

    insertRow :: SQLite.Connection -> a -> IO (Key a)

    -- TODO (thomas.tuegel): Implement this!
    -- selectRow :: SQLite.Connection -> Key a -> IO a
