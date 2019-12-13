module Kore.Step.AxiomPattern
    ( HasLeftPattern (..)
    , HasRequiresPredicate (..)
    , HasRefreshPattern (..)
    , HasMapVariables (..)
    ) where

import Kore.Internal.TermLike
    ( TermLike
    )
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Substitute
    ( SubstitutionVariable
    )
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (..)
    )
import Kore.Variables.Fresh
    ( Renaming
    )

class HasLeftPattern rule variable where
    leftPattern :: rule variable -> TermLike variable 

class HasRequiresPredicate rule variable where
    requiresPredicate :: rule variable -> Predicate variable 

class SubstitutionVariable variable => HasRefreshPattern rule variable where
    {- | Refresh the variables of a rule

    The free variables of a rule are implicitly quantified, so they are
    renamed to avoid collision with any variables in the given set.

     -}
    refreshPattern
        :: FreeVariables variable  -- ^ Variables to avoid
        -> rule variable
        -> (Renaming variable, rule variable)

class HasMapVariables rule where
    {- | Apply the given function to all variables in a 'RulePattern'.
     -}
    mapVariables
        :: Ord variable2
        => (variable1 -> variable2)
        -> rule variable1
        -> rule variable2