{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (..)
    , freeVariable
    , isFreeVariable
    , bindVariable
    , mapFreeVariables
    , traverseFreeVariables
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

import Kore.SubstVar ( SubstVar )

newtype FreeVariables variable =
    FreeVariables { getFreeVariables :: Set (SubstVar variable) }
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

bindVariable
    :: Ord variable
    => SubstVar variable
    -> FreeVariables variable
    -> FreeVariables variable
bindVariable variable (FreeVariables freeVariables) =
    FreeVariables (Set.delete variable freeVariables)
{-# INLINE bindVariable #-}

isFreeVariable :: Ord variable => SubstVar variable -> FreeVariables variable -> Bool
isFreeVariable variable (FreeVariables freeVariables) =
    Set.member variable freeVariables
{-# INLINE isFreeVariable #-}

freeVariable :: Ord variable => SubstVar variable -> FreeVariables variable
freeVariable variable = FreeVariables (Set.singleton variable)
{-# INLINE freeVariable #-}

mapFreeVariables
    :: Ord variable2
    => (variable1 -> variable2)
    -> FreeVariables variable1 -> FreeVariables variable2
mapFreeVariables mapping (FreeVariables freeVariables) =
    FreeVariables (Set.map (fmap mapping) freeVariables)
{-# INLINE mapFreeVariables #-}

traverseFreeVariables
    :: (Applicative f, Ord variable2)
    => (variable1 -> f variable2)
    -> FreeVariables variable1 -> f (FreeVariables variable2)
traverseFreeVariables traversing (FreeVariables freeVariables) =
    FreeVariables . Set.fromList
    <$> Traversable.traverse (traverse traversing) (Set.toList freeVariables)
{-# INLINE traverseFreeVariables #-}
