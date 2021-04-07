{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

Foreign keys for SQL tables.
-}
module SQL.Key (
    Key (..),
) where

import Data.Int
    ( Int64
    )
import Debug
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import Prelude.Kore

-- | A foreign key into the table for type @a@.
newtype Key a = Key {getKey :: Int64}
    deriving stock (Eq, Ord, Read, Show)
    deriving stock (Functor, Foldable)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
