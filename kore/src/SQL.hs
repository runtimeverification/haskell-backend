module SQL
    ( Key (..)
    , Table (..)
    , SQLite.Connection
    ) where

import Data.Int
    ( Int64
    )
import qualified Database.SQLite.Simple as SQLite

newtype Key a = Key { getKey :: Int64 }

class Table a where
    createTable :: SQLite.Connection -> proxy a -> IO ()

    -- TODO (thomas.tuegel): Implement these!
    -- insertRow :: SQLite.Connection -> a -> IO (Key a)
    -- selectRow :: SQLite.Connection -> Key a -> IO a
