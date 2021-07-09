{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause

Target specific variables for unification.
-}
module Kore.Variables.Target (
    Target (..),
    unTarget,
    unTargetElement,
    unTargetSet,
    mkElementTarget,
    mkSetTarget,
    mkUnifiedTarget,
    isTarget,
    mkElementNonTarget,
    mkSetNonTarget,
    mkUnifiedNonTarget,
    isNonTarget,
    targetIfEqual,
    isSomeTargetName,
    isSomeNonTargetName,
) where

import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Debug
import Kore.Internal.Variable
import Kore.Unparser (
    Unparse (..),
 )
import Kore.Variables.Fresh (
    FreshPartialOrd (..),
 )
import Prelude.Kore

{- | Distinguish variables by their source.

'Target' variables always compare 'LT' 'NonTarget' variables under
'SubstitutionOrd', so that the unification procedure prefers to generate
substitutions for 'Target' variables instead of 'NonTarget' variables.
-}
data Target variable
    = Target !variable
    | NonTarget !variable
    deriving stock (Show)
    deriving stock (Foldable, Functor, Traversable)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Eq variable => Eq (Target variable) where
    (==) a b = unTarget a == unTarget b
    {-# INLINE (==) #-}

instance Ord variable => Ord (Target variable) where
    compare a b = compare (unTarget a) (unTarget b)
    {-# INLINE compare #-}

instance Hashable variable => Hashable (Target variable) where
    hashWithSalt salt target = hashWithSalt salt (unTarget target)
    {-# INLINE hashWithSalt #-}

-- | Prefer substitutions for 'isTarget' variables.
instance SubstitutionOrd variable => SubstitutionOrd (Target variable) where
    compareSubstitution (Target _) (NonTarget _) = LT
    compareSubstitution (NonTarget _) (Target _) = GT
    compareSubstitution variable1 variable2 =
        on compareSubstitution unTarget variable1 variable2

unTarget :: Target variable -> variable
unTarget (Target variable) = variable
unTarget (NonTarget variable) = variable
{-# INLINE unTarget #-}

unTargetElement :: ElementVariable (Target variable) -> ElementVariable variable
unTargetElement = (fmap . fmap) unTarget

unTargetSet :: SetVariable (Target variable) -> SetVariable variable
unTargetSet = (fmap . fmap) unTarget

mkElementTarget ::
    ElementVariable variable ->
    ElementVariable (Target variable)
mkElementTarget = (fmap . fmap) Target

mkSetTarget ::
    SetVariable variable ->
    SetVariable (Target variable)
mkSetTarget = (fmap . fmap) Target

mkUnifiedTarget :: AdjSomeVariableName (variable -> Target variable)
mkUnifiedTarget = pure Target

isTarget :: Target variable -> Bool
isTarget (Target _) = True
isTarget (NonTarget _) = False

mkElementNonTarget ::
    ElementVariable variable ->
    ElementVariable (Target variable)
mkElementNonTarget = (fmap . fmap) NonTarget

mkSetNonTarget ::
    SetVariable variable ->
    SetVariable (Target variable)
mkSetNonTarget = (fmap . fmap) NonTarget

mkUnifiedNonTarget :: AdjSomeVariableName (variable -> Target variable)
mkUnifiedNonTarget = pure NonTarget

isNonTarget :: Target variable -> Bool
isNonTarget = not . isTarget

isSomeTargetName :: SomeVariableName (Target variable) -> Bool
isSomeTargetName (SomeVariableNameElement (ElementVariableName variable)) =
    isTarget variable
isSomeTargetName (SomeVariableNameSet (SetVariableName variable)) =
    isTarget variable

isSomeNonTargetName :: SomeVariableName (Target variable) -> Bool
isSomeNonTargetName = not . isSomeTargetName

instance From variable1 variable2 => From variable1 (Target variable2) where
    from = Target . from @variable1 @variable2
    {-# INLINE from #-}

instance From variable1 variable2 => From (Target variable1) variable2 where
    from = from @variable1 @variable2 . unTarget
    {-# INLINE from #-}

instance FreshPartialOrd variable => FreshPartialOrd (Target variable) where
    minBoundName =
        \case
            Target var -> Target (minBoundName var)
            NonTarget var -> NonTarget (minBoundName var)
    {-# INLINE minBoundName #-}

    maxBoundName =
        \case
            Target var -> Target (maxBoundName var)
            NonTarget var -> NonTarget (maxBoundName var)
    {-# INLINE maxBoundName #-}

    nextName name1 name2 = traverse (flip nextName (unTarget name2)) name1
    {-# INLINE nextName #-}

-- | Ensures that fresh variables are unique under 'unwrapStepperVariable'.
instance FreshPartialOrd variable => FreshName (Target variable)

instance Unparse variable => Unparse (Target variable) where
    unparse (Target var) = unparse var
    unparse (NonTarget var) = unparse var
    unparse2 (Target var) = unparse2 var
    unparse2 (NonTarget var) = unparse2 var

targetIfEqual :: Eq variable => variable -> variable -> Target variable
targetIfEqual boundVariableName variableName =
    if boundVariableName == variableName
        then Target variableName
        else NonTarget variableName
