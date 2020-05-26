{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

 -}

module Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , toList
    , toSet
    , nullFreeVariables
    , freeVariable
    , isFreeVariable
    , bindVariable
    , bindVariables
    , mapFreeVariables
    , traverseFreeVariables
    , getFreeElementVariables
    , HasFreeVariables (..)
    ) where

import Prelude.Kore

import Control.DeepSeq
import qualified Data.Foldable as Foldable
import Data.Functor.Const
import Data.Map.Strict
    ( Map
    )
import qualified Data.Map.Strict as Map
import Data.Set
    ( Set
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Syntax.ElementVariable
import Kore.Syntax.Variable
import Kore.Variables.UnifiedVariable

newtype FreeVariables variable =
    FreeVariables { getFreeVariables :: Map (UnifiedVariable variable) Sort }
    deriving GHC.Generic
    deriving (Eq, Ord, Show)
    deriving (Semigroup, Monoid)

instance SOP.Generic (FreeVariables variable)

instance SOP.HasDatatypeInfo (FreeVariables variable)

instance Debug variable => Debug (FreeVariables variable)

instance (Debug variable, Diff variable) => Diff (FreeVariables variable)

instance NFData variable => NFData (FreeVariables variable)

instance Hashable variable => Hashable (FreeVariables variable) where
    hashWithSalt salt = hashWithSalt salt . toList
    {-# INLINE hashWithSalt #-}

instance
    NamedVariable variable
    => Synthetic (FreeVariables variable) (Const (UnifiedVariable variable))
  where
    synthetic (Const var) = freeVariable var
    {-# INLINE synthetic #-}

instance From (FreeVariables variable) [UnifiedVariable variable] where
    from = toList
    {-# INLINE from #-}

instance From (FreeVariables variable) (Set (UnifiedVariable variable)) where
    from = toSet
    {-# INLINE from #-}

toList :: FreeVariables variable -> [UnifiedVariable variable]
toList = Map.keys . getFreeVariables
{-# INLINE toList #-}

fromList
    :: NamedVariable variable
    => [UnifiedVariable variable]
    -> FreeVariables variable
fromList = foldMap freeVariable
{-# INLINE fromList #-}

toSet :: FreeVariables variable -> Set (UnifiedVariable variable)
toSet = Map.keysSet . getFreeVariables
{-# INLINE toSet #-}

nullFreeVariables :: FreeVariables variable -> Bool
nullFreeVariables = Map.null . getFreeVariables
{-# INLINE nullFreeVariables #-}

bindVariable
    :: Ord variable
    => UnifiedVariable variable
    -> FreeVariables variable
    -> FreeVariables variable
bindVariable variable (FreeVariables freeVars) =
    FreeVariables (Map.delete variable freeVars)
{-# INLINE bindVariable #-}

bindVariables
    :: Ord variable
    => Foldable f
    => f (UnifiedVariable variable)
    -> FreeVariables variable
    -> FreeVariables variable
bindVariables bound free =
    Foldable.foldl' (flip bindVariable) free bound
{-# INLINE bindVariables #-}

isFreeVariable
    :: Ord variable
    => UnifiedVariable variable -> FreeVariables variable -> Bool
isFreeVariable variable (FreeVariables freeVars) =
    Map.member variable freeVars
{-# INLINE isFreeVariable #-}

freeVariable
    :: NamedVariable variable
    => UnifiedVariable variable
    -> FreeVariables variable
freeVariable variable =
    FreeVariables (Map.singleton variable variableSort1)
  where
    Variable1 { variableSort1 } = toVariable1 variable
{-# INLINE freeVariable #-}

mapFreeVariables
    ::  (NamedVariable variable1, NamedVariable variable2)
    =>  AdjSomeVariableName
            (VariableNameOf variable1 -> VariableNameOf variable2)
    ->  FreeVariables variable1 -> FreeVariables variable2
mapFreeVariables adj = fromList . map (mapUnifiedVariable adj) . toList
{-# INLINE mapFreeVariables #-}

traverseFreeVariables
    ::  Applicative f
    =>  (NamedVariable variable1, NamedVariable variable2)
    =>  AdjSomeVariableName
            (VariableNameOf variable1 -> f (VariableNameOf variable2))
    ->  FreeVariables variable1 -> f (FreeVariables variable2)
traverseFreeVariables adj =
    fmap fromList . traverse (traverseUnifiedVariable adj) . toList
{-# INLINE traverseFreeVariables #-}

{- | Extracts the list of free element variables
-}
getFreeElementVariables :: FreeVariables variable -> [ElementVariable variable]
getFreeElementVariables = mapMaybe extractElementVariable . toList

-- TODO (thomas.tuegel): Use an associated type family with HasFreeVariables to
-- fix type inference.

-- | Class for extracting the free variables of a pattern, term, rule, ...
class HasFreeVariables pat variable where
    freeVariables :: pat -> FreeVariables variable

instance Ord variable => HasFreeVariables () variable where
    freeVariables = const mempty
