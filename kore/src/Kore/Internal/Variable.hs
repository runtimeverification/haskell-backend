{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Internal.Variable (
    SubstitutionOrd (..),
    InternalVariable,
    FreshName,
    FreshPartialOrd,
    module Kore.Syntax.Variable,
) where

import Data.Void
import Kore.Debug (
    Debug,
 )
import Kore.Syntax.Variable
import Kore.Unparser (
    Unparse,
 )
import Kore.Variables.Fresh (
    FreshName,
    FreshPartialOrd,
 )
import Prelude.Kore

{- | @SubstitutionOrd@ orders variables for substitution.

When unifying or matching two variables @x@ and @y@, we prefer to order the
solution so that we get a substitution for the lesser of the two, as computed by
'comparePriority'.

Equality:

prop> (compareSubstitution a b == EQ) = (a == b)

Note: the equality law implies reflexivity.

Antisymmetry:

prop> (compareSubstitution a b == LT) = (compareSubstitution b a == GT)

Transitivity:

prop> (compareSubstitution x y == compareSubstitution y z) == (compareSubstitution x y == compareSubstitution x z)
-}
class Eq variable => SubstitutionOrd variable where
    compareSubstitution :: variable -> variable -> Ordering

instance SubstitutionOrd Void where
    compareSubstitution = \case
    {-# INLINE compareSubstitution #-}

instance SubstitutionOrd VariableName where
    compareSubstitution = compare
    {-# INLINE compareSubstitution #-}

instance SubstitutionOrd variable => SubstitutionOrd (ElementVariableName variable) where
    compareSubstitution = on compareSubstitution unElementVariableName
    {-# INLINE compareSubstitution #-}

instance SubstitutionOrd variable => SubstitutionOrd (SetVariableName variable) where
    compareSubstitution = on compareSubstitution unSetVariableName
    {-# INLINE compareSubstitution #-}

instance SubstitutionOrd variable => SubstitutionOrd (SomeVariableName variable) where
    compareSubstitution
        (SomeVariableNameElement x)
        (SomeVariableNameElement y) =
            compareSubstitution x y
    compareSubstitution (SomeVariableNameElement _) _ = LT
    compareSubstitution
        (SomeVariableNameSet x)
        (SomeVariableNameSet y) =
            compareSubstitution x y
    compareSubstitution (SomeVariableNameSet _) _ = GT
    {-# INLINE compareSubstitution #-}

instance SubstitutionOrd variable => SubstitutionOrd (Variable variable) where
    compareSubstitution = on compareSubstitution variableName
    {-# INLINE compareSubstitution #-}

{- | 'InternalVariable' is the basic constraint on variable types.

All variable types must implement these constraints, and in practice most
functions which are polymorphic over the variable type require most or all of
these constraints.
-}
type InternalVariable variable =
    ( Hashable variable
    , Ord variable
    , SubstitutionOrd variable
    , Debug variable
    , Show variable
    , Unparse variable
    , From VariableName variable
    , From variable VariableName
    , FreshPartialOrd variable
    , FreshName variable
    , Typeable variable
    )
