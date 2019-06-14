{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (..)
    , null, insert, delete, member, singleton, map, traverse
    ) where

import           Control.DeepSeq
import           Data.Hashable
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC
import           Prelude hiding
                 ( map, null, traverse )

import Kore.Debug

newtype FreeVariables variable =
    FreeVariables { getFreeVariables :: Set variable }
    deriving GHC.Generic
    deriving (Eq, Show)
    deriving Foldable
    deriving (Semigroup, Monoid)

instance SOP.Generic (FreeVariables variable)

instance SOP.HasDatatypeInfo (FreeVariables variable)

instance Debug variable => Debug (FreeVariables variable)

instance NFData variable => NFData (FreeVariables variable)

instance Hashable variable => Hashable (FreeVariables variable) where
    hashWithSalt salt (FreeVariables freeVariables) =
        hashWithSalt salt (Set.toList freeVariables)

null :: FreeVariables variable -> Bool
null (FreeVariables freeVariables) = Set.null freeVariables
{-# INLINE null #-}

insert
    :: Ord variable
    => variable
    -> FreeVariables variable
    -> FreeVariables variable
insert variable (FreeVariables freeVariables) =
    FreeVariables (Set.insert variable freeVariables)
{-# INLINE insert #-}

delete
    :: Ord variable
    => variable
    -> FreeVariables variable
    -> FreeVariables variable
delete variable (FreeVariables freeVariables) =
    FreeVariables (Set.delete variable freeVariables)
{-# INLINE delete #-}

member :: Ord variable => variable -> FreeVariables variable -> Bool
member variable (FreeVariables freeVariables) =
    Set.member variable freeVariables
{-# INLINE member #-}

singleton :: Ord variable => variable -> FreeVariables variable
singleton variable = FreeVariables (Set.singleton variable)
{-# INLINE singleton #-}

map
    :: Ord variable2
    => (variable1 -> variable2)
    -> FreeVariables variable1 -> FreeVariables variable2
map mapping (FreeVariables freeVariables) =
    FreeVariables (Set.map mapping freeVariables)
{-# INLINE map #-}

traverse
    :: (Applicative f, Ord variable2)
    => (variable1 -> f variable2)
    -> FreeVariables variable1 -> f (FreeVariables variable2)
traverse traversing (FreeVariables freeVariables) =
    FreeVariables . Set.fromList
    <$> Traversable.traverse traversing (Set.toList freeVariables)
{-# INLINE traverse #-}
