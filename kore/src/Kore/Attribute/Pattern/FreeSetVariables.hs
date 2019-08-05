{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.FreeSetVariables
    ( FreeSetVariables (..)
    , freeSetVariable
    , isFreeSetVariable
    , bindSetVariable
    , mapFreeSetVariables
    , traverseFreeSetVariables
    ) where

import           Control.DeepSeq
import           Data.Hashable
import           Data.Set
                 ( Set )
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug

newtype FreeSetVariables variable =
    FreeSetVariables { getFreeSetVariables :: Set variable }
    deriving GHC.Generic
    deriving (Eq, Show)
    deriving Foldable
    deriving (Semigroup, Monoid)

instance SOP.Generic (FreeSetVariables variable)

instance SOP.HasDatatypeInfo (FreeSetVariables variable)

instance Debug variable => Debug (FreeSetVariables variable)

instance NFData variable => NFData (FreeSetVariables variable)

instance Hashable variable => Hashable (FreeSetVariables variable) where
    hashWithSalt salt (FreeSetVariables freeSetVariables) =
        hashWithSalt salt (Set.toList freeSetVariables)

bindSetVariable
    :: Ord variable
    => variable
    -> FreeSetVariables variable
    -> FreeSetVariables variable
bindSetVariable variable (FreeSetVariables freeSetVariables) =
    FreeSetVariables (Set.delete variable freeSetVariables)
{-# INLINE bindSetVariable #-}

isFreeSetVariable :: Ord variable => variable -> FreeSetVariables variable -> Bool
isFreeSetVariable variable (FreeSetVariables freeSetVariables) =
    Set.member variable freeSetVariables
{-# INLINE isFreeSetVariable #-}

freeSetVariable :: Ord variable => variable -> FreeSetVariables variable
freeSetVariable variable = FreeSetVariables (Set.singleton variable)
{-# INLINE freeSetVariable #-}

mapFreeSetVariables
    :: Ord variable2
    => (variable1 -> variable2)
    -> FreeSetVariables variable1 -> FreeSetVariables variable2
mapFreeSetVariables mapping (FreeSetVariables freeSetVariables) =
    FreeSetVariables (Set.map mapping freeSetVariables)
{-# INLINE mapFreeSetVariables #-}

traverseFreeSetVariables
    :: (Applicative f, Ord variable2)
    => (variable1 -> f variable2)
    -> FreeSetVariables variable1 -> f (FreeSetVariables variable2)
traverseFreeSetVariables traversing (FreeSetVariables freeSetVariables) =
    FreeSetVariables . Set.fromList
    <$> Traversable.traverse traversing (Set.toList freeSetVariables)
{-# INLINE traverseFreeSetVariables #-}
