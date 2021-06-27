{- |
Copyright   : (c) Runtime Verification, 2021
License     : NCSA
-}
module Kore.Internal.Substitute (
    Substitute (..),
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
class
    (InternalVariable variable, HasFreeVariables child variable) =>
    Substitute variable child
        | child -> variable
    where
    -- | The type of terms used to replace variables under substitution.
    type TermType child :: Type

    -- | Apply a substitution: replace variables with terms from a 'Map'.
    substitute ::
        Map (SomeVariableName variable) (TermType child) ->
        child ->
        child
