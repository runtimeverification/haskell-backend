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
import Kore.Internal.Variable (
    SomeVariable,
    SomeVariableName,
 )

class
    HasFreeVariables child variable =>
    Substitute variable child
        | child -> variable
    where
    type SubstituteTerm child :: Type

    substitute ::
        Map (SomeVariableName variable) (SubstituteTerm child) ->
        child ->
        child

    rename ::
        Map (SomeVariableName variable) (SomeVariable variable) ->
        child ->
        child