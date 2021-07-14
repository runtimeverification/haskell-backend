{- |
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}
module Kore.Substitute (
    Substitute (..),
    NormalSubstitution,
    NormalRenaming,
    refreshElementBinder,
) where

import Data.Kind (
    Type,
 )
import Data.Map.Strict (
    Map,
 )
import qualified Data.Map.Strict as Map
import Data.Set (
    Set,
 )
import Kore.Attribute.Pattern.FreeVariables (
    HasFreeVariables,
 )
import Kore.Internal.Variable
import Kore.Variables.Binding (
    Binder (..),
 )
import Kore.Variables.Fresh (refreshElementVariable)
import Prelude.Kore

-- | @Substitute@ implements capture-avoiding substitution over many types.
class HasFreeVariables child (VariableNameType child) => Substitute child where
    -- | The type of terms used to replace variables under substitution.
    type TermType child :: Type

    -- | The type of variable names to be replaced under substitution.
    type VariableNameType child :: Type

    -- | Apply a substitution: replace variables with terms from a 'Map'. The
    -- 'NormalSubstitution' is assumed to be proper (none of the variables on
    -- the left appear in any term on the right), but this is not checked.
    substitute :: NormalSubstitution child -> child -> child

    -- | Rename variables from a 'Map'. The 'NormalRenaming' is assumed to be
    -- proper (none of the variables on the left appear on the right), but this
    -- is not checked.
    rename :: NormalRenaming child -> child -> child

{- | A @NormalSubstitution@ maps variable names to terms so that the former may
 be replaced by the latter. In a proper @NormalSubstitution@, none of the
 variables on the left appear in any of the terms on the right.
-}
type NormalSubstitution child =
    Map (SomeVariableName (VariableNameType child)) (TermType child)

{- | A @NormalRenaming@ maps variable names to variables so that the former may
 be renamed based on the latter. In a proper @NormalRenaming@, none of the
 variable on the left appear in any of the terms on the right.
-}
type NormalRenaming child =
    Map
        (SomeVariableName (VariableNameType child))
        -- TODO (thomas.tuegel): Arguably, the values below should be only
        -- 'SomeVariableName' and not 'SomeVariable'.
        (SomeVariable (VariableNameType child))

instance
    (Substitute child, Ord (VariableNameType child)) =>
    Substitute [child]
    where
    type TermType [child] = TermType child
    type VariableNameType [child] = VariableNameType child

    substitute subst = fmap (substitute subst)
    {-# INLINE substitute #-}

    rename renaming = fmap (rename renaming)
    {-# INLINE rename #-}

refreshElementBinder ::
    forall variable child.
    Substitute child =>
    VariableNameType child ~ variable =>
    FreshPartialOrd variable =>
    Set (SomeVariableName variable) ->
    Binder (ElementVariable variable) child ->
    Binder (ElementVariable variable) child
refreshElementBinder avoiding binder =
    do
        binderVariable' <- refreshElementVariable avoiding binderVariable
        let someVariableName =
                inject @(SomeVariableName variable)
                    (variableName binderVariable)
            someVariable' = inject @(SomeVariable _) binderVariable'
            renaming = Map.singleton someVariableName someVariable'
            binderChild' = rename renaming binderChild
        return
            Binder
                { binderVariable = binderVariable'
                , binderChild = binderChild'
                }
        & fromMaybe binder
  where
    Binder{binderVariable, binderChild} = binder
