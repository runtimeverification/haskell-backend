{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (..)
    , HasFreeVariables (..)
    , freeVariable
    , isFreeVariable
    , bindVariable
    , mapFreeVariables
    , traverseFreeVariables
    , getFreeElementVariables
    ) where

import Prelude.Kore

import Control.DeepSeq
import Data.Functor.Const
import Data.Hashable
import Data.Maybe
    ( mapMaybe
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set
import qualified Data.Traversable as Traversable
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Syntax.ElementVariable
import Kore.Variables.UnifiedVariable

newtype FreeVariables variable =
    FreeVariables { getFreeVariables :: Set (UnifiedVariable variable) }
    deriving GHC.Generic
    deriving (Eq, Show)
    deriving Foldable
    deriving (Semigroup, Monoid)

instance SOP.Generic (FreeVariables variable)

instance SOP.HasDatatypeInfo (FreeVariables variable)

instance Debug variable => Debug (FreeVariables variable)

instance (Debug variable, Diff variable) => Diff (FreeVariables variable)

instance NFData variable => NFData (FreeVariables variable)

instance Hashable variable => Hashable (FreeVariables variable) where
    hashWithSalt salt (FreeVariables freeVars) =
        hashWithSalt salt (Set.toList freeVars)

instance Synthetic (FreeVariables variable) (Const (UnifiedVariable variable))
  where
    synthetic (Const var) = freeVariable var
    {-# INLINE synthetic #-}

bindVariable
    :: Ord variable
    => UnifiedVariable variable
    -> FreeVariables variable
    -> FreeVariables variable
bindVariable variable (FreeVariables freeVars) =
    FreeVariables (Set.delete variable freeVars)
{-# INLINE bindVariable #-}

isFreeVariable
    :: Ord variable
    => UnifiedVariable variable -> FreeVariables variable -> Bool
isFreeVariable variable (FreeVariables freeVars) =
    Set.member variable freeVars
{-# INLINE isFreeVariable #-}

freeVariable :: UnifiedVariable variable -> FreeVariables variable
freeVariable variable = FreeVariables (Set.singleton variable)
{-# INLINE freeVariable #-}

mapFreeVariables
    :: Ord variable2
    => (variable1 -> variable2)
    -> FreeVariables variable1 -> FreeVariables variable2
mapFreeVariables mapping (FreeVariables freeVars) =
    FreeVariables (Set.map (fmap mapping) freeVars)
{-# INLINE mapFreeVariables #-}

traverseFreeVariables
    :: (Applicative f, Ord variable2)
    => (variable1 -> f variable2)
    -> FreeVariables variable1 -> f (FreeVariables variable2)
traverseFreeVariables traversing (FreeVariables freeVars) =
    FreeVariables . Set.fromList
    <$> Traversable.traverse (traverse traversing) (Set.toList freeVars)
{-# INLINE traverseFreeVariables #-}

{- | Extracts the list of free element variables
-}
getFreeElementVariables :: FreeVariables variable -> [ElementVariable variable]
getFreeElementVariables =
    mapMaybe extractElementVariable . Set.toList . getFreeVariables

-- | Class for extracting the free variables of a pattern, term, rule, ...
class HasFreeVariables pat variable where
    freeVariables :: pat -> FreeVariables variable

instance Ord variable => HasFreeVariables () variable where
    freeVariables = const mempty
