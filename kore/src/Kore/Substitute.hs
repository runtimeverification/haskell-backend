{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Substitute (
    Substitute (..),
    NormalSubstitution,
    NormalRenaming,
) where

import Data.Kind (
    Type,
 )
import Data.Map.Strict (
    Map,
 )
import Kore.Attribute.Pattern.FreeVariables (
    HasFreeVariables,
 )
import Kore.Internal.Variable

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
