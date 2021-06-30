{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
    toList,
    toSet,
    toNames,
    nullFreeVariables,
    emptyFreeVariables,
    freeVariable,
    isFreeVariable,
    bindVariable,
    bindVariables,
    mapFreeVariables,
    traverseFreeVariables,
    getFreeElementVariables,
    HasFreeVariables (..),
    occursIn,
    freeVariableNames,
) where

import Data.Functor.Const
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Set (
    Set,
 )
import qualified Data.Set as Set
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Synthetic
import Kore.Debug
import Kore.Sort
import Kore.Syntax.Variable
import Prelude.Kore hiding (
    toList,
 )

newtype FreeVariables variable = FreeVariables
    { getFreeVariables :: Map (SomeVariableName variable) Sort
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)
    deriving newtype (Semigroup, Monoid)

instance Hashable variable => Hashable (FreeVariables variable) where
    hashWithSalt salt = hashWithSalt salt . toList
    {-# INLINE hashWithSalt #-}

instance
    Synthetic
        (FreeVariables variable)
        (Const (SomeVariable variable))
    where
    synthetic (Const var) = freeVariable var
    {-# INLINE synthetic #-}

instance From (FreeVariables variable) [SomeVariable variable] where
    from = toList
    {-# INLINE from #-}

instance From (FreeVariables variable) (Set (SomeVariable variable)) where
    from = toSet
    {-# INLINE from #-}

instance From (FreeVariables variable) (Set (SomeVariableName variable)) where
    from = toNames
    {-# INLINE from #-}

toList :: FreeVariables variable -> [SomeVariable variable]
toList = map (uncurry Variable) . Map.toAscList . getFreeVariables
{-# INLINE toList #-}

fromList ::
    Ord variable =>
    [SomeVariable variable] ->
    FreeVariables variable
fromList = foldMap freeVariable
{-# INLINE fromList #-}

toSet :: FreeVariables variable -> Set (SomeVariable variable)
toSet =
    Set.fromDistinctAscList
        . map (uncurry Variable)
        . Map.toAscList
        . getFreeVariables
{-# INLINE toSet #-}

toNames :: FreeVariables variable -> Set (SomeVariableName variable)
toNames = Map.keysSet . getFreeVariables
{-# INLINE toNames #-}

nullFreeVariables :: FreeVariables variable -> Bool
nullFreeVariables = Map.null . getFreeVariables
{-# INLINE nullFreeVariables #-}

emptyFreeVariables :: FreeVariables variable
emptyFreeVariables = FreeVariables Map.empty
{-# INLINE emptyFreeVariables #-}

bindVariable ::
    Ord variable =>
    SomeVariable variable ->
    FreeVariables variable ->
    FreeVariables variable
bindVariable Variable{variableName} (FreeVariables freeVars) =
    FreeVariables (Map.delete variableName freeVars)
{-# INLINE bindVariable #-}

bindVariables ::
    Ord variable =>
    Foldable f =>
    f (SomeVariable variable) ->
    FreeVariables variable ->
    FreeVariables variable
bindVariables bound free = foldl' (flip bindVariable) free bound
{-# INLINE bindVariables #-}

isFreeVariable ::
    Ord variable =>
    SomeVariableName variable ->
    FreeVariables variable ->
    Bool
isFreeVariable someVariableName (FreeVariables freeVars) =
    Map.member someVariableName freeVars
{-# INLINE isFreeVariable #-}

freeVariable :: SomeVariable variable -> FreeVariables variable
freeVariable Variable{variableName, variableSort} =
    FreeVariables (Map.singleton variableName variableSort)
{-# INLINE freeVariable #-}

mapFreeVariables ::
    Ord variable2 =>
    AdjSomeVariableName (variable1 -> variable2) ->
    FreeVariables variable1 ->
    FreeVariables variable2
mapFreeVariables adj = fromList . map (mapSomeVariable adj) . toList
{-# INLINE mapFreeVariables #-}

traverseFreeVariables ::
    Applicative f =>
    Ord variable2 =>
    AdjSomeVariableName (variable1 -> f variable2) ->
    FreeVariables variable1 ->
    f (FreeVariables variable2)
traverseFreeVariables adj =
    fmap fromList . traverse (traverseSomeVariable adj) . toList
{-# INLINE traverseFreeVariables #-}

-- | Extracts the list of free element variables
getFreeElementVariables :: FreeVariables variable -> [ElementVariable variable]
getFreeElementVariables = mapMaybe retractElementVariable . toList

-- TODO (thomas.tuegel): Use an associated type family with HasFreeVariables to
-- fix type inference.

-- | Class for extracting the free variables of a pattern, term, rule, ...
class HasFreeVariables pat variable where
    freeVariables :: pat -> FreeVariables variable

instance HasFreeVariables () variable where
    freeVariables = const emptyFreeVariables

instance
    (HasFreeVariables child variable, Ord variable) =>
    HasFreeVariables [child] variable
    where
    freeVariables = foldMap freeVariables
    {-# INLINE freeVariables #-}

instance
    (HasFreeVariables a variable, HasFreeVariables b variable, Ord variable) =>
    HasFreeVariables (a, b) variable
    where
    freeVariables = \(a, b) -> freeVariables a <> freeVariables b
    {-# INLINE freeVariables #-}

-- | Does the named variable occur free in the pattern?
occursIn ::
    Ord variable =>
    HasFreeVariables thing variable =>
    SomeVariableName variable ->
    thing ->
    Bool
occursIn variableName thing =
    isFreeVariable variableName (freeVariables thing)

freeVariableNames ::
    HasFreeVariables thing variable =>
    thing ->
    Set (SomeVariableName variable)
freeVariableNames = toNames . freeVariables
