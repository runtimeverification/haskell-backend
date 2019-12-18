{-|
Description : Common functionality for RulePattern and EqualityPattern
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Step.AxiomPattern
    ( HasLeftPattern (..)
    , HasRequiresPredicate (..)
    , HasRefreshPattern (..)
    , HasMapVariables (..)
    ) where

import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (..)
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.TermLike
    ( TermLike
    )
import Kore.Substitute
    ( SubstitutionVariable
    )
import Kore.Variables.Fresh
    ( Renaming
    )

{-| Should be implemented for rules having a clearly identifiable
left-hand-side pattern used for matching / unifying with the configuration.
-}
class HasLeftPattern rule variable where
    leftPattern :: rule variable -> TermLike variable

{-| Should be implemented for rules having a clearly identifiable
precondition for the application of the rule (a requires clause).
-}
class HasRequiresPredicate rule variable where
    requiresPredicate :: rule variable -> Predicate variable

{-| Refresh the variables of a rule

The free variables of a rule are implicitly quantified, so they are
renamed to avoid collision with any variables in the given set.

 -}
class SubstitutionVariable variable => HasRefreshPattern rule variable where
    refreshPattern
        :: FreeVariables variable  -- ^ Variables to avoid
        -> rule variable
        -> (Renaming variable, rule variable)

{-| Apply a given function to all variables in a 'pattern'.
 -}
class HasMapVariables rule where
    mapVariables
        :: Ord variable2
        => (variable1 -> variable2)
        -> rule variable1
        -> rule variable2
