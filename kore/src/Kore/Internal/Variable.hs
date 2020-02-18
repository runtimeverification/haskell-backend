{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Internal.Variable
    ( SubstitutionOrd (..)
    , InternalVariable
    , FreshVariable
    , FreshPartialOrd
    , module Kore.Syntax.ElementVariable
    , module Kore.Syntax.SetVariable
    , module Kore.Syntax.Variable
    ) where

import Prelude.Kore

import Kore.Debug
    ( Debug
    )
import Kore.Syntax.ElementVariable
import Kore.Syntax.SetVariable
import Kore.Syntax.Variable
import Kore.Unparser
    ( Unparse
    )
import Kore.Variables.Fresh
    ( FreshPartialOrd
    , FreshVariable
    )

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

instance SubstitutionOrd Variable where
    compareSubstitution = compare
    {-# INLINE compareSubstitution #-}

instance SubstitutionOrd Concrete where
    compareSubstitution = \case {}
    {-# INLINE compareSubstitution #-}

instance
    SubstitutionOrd variable => SubstitutionOrd (ElementVariable variable)
  where
    compareSubstitution = on compareSubstitution getElementVariable
    {-# INLINE compareSubstitution #-}

instance
    SubstitutionOrd variable => SubstitutionOrd (SetVariable variable)
  where
    compareSubstitution = on compareSubstitution getSetVariable
    {-# INLINE compareSubstitution #-}

{- | 'InternalVariable' is the basic constraint on variable types.

All variable types must implement these constraints, and in practice most
functions which are polymorphic over the variable type require most or all of
these constraints.

 -}
type InternalVariable variable =
    ( Ord variable, SubstitutionOrd variable
    , Debug variable, Show variable, Unparse variable
    , VariableName variable, SortedVariable variable
    , FreshPartialOrd variable, FreshVariable variable
    )
