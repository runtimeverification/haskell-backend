{-|
Module      : Kore.Step.PredicateSubstitution
Description : Data structures and functions for manipulating
              PredicateSubstitution, i.e. a representation of patterns
              optimized for the stepper.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.PredicateSubstitution
    ( CommonPredicateSubstitution
    , PredicateSubstitution (..)
    , bottom
    , top
    ) where

import Kore.AST.Common
       ( Variable )
import Kore.AST.MetaOrObject
import Kore.Predicate.Predicate
       ( Predicate, makeFalsePredicate, makeTruePredicate )
import Kore.Unification.UnificationSolution
       ( UnificationSubstitution )

{-|'PredicateSubstitution' is a representation of a specific type of
PureMLPattern that occurs in certain cases when executing Kore.
-}
data PredicateSubstitution level variable = PredicateSubstitution
    { predicate    :: !(Predicate level variable)
    -- ^ pattern that only evaluates to Top or Bottom.
    , substitution :: !(UnificationSubstitution level variable)
    -- ^ special kind of predicate of the type
    -- variable1 = term1 /\ variable2 = term2 /\ ...
    }
    deriving (Eq, Show)

{-| 'CommonPredicateSubstitution' particularizes PredicateSubstitution to
Variable.
-}
type CommonPredicateSubstitution level = PredicateSubstitution level Variable

{-|'bottom' is an expanded pattern that has a bottom condition and that
should become Bottom when transformed to a ML pattern.
-}
bottom :: MetaOrObject level => PredicateSubstitution level variable
bottom =
    PredicateSubstitution
        { predicate = makeFalsePredicate
        , substitution = []
        }

{-|'top' is an expanded pattern that has a top condition and that
should become Top when transformed to a ML pattern.
-}
top :: MetaOrObject level => PredicateSubstitution level variable
top =
    PredicateSubstitution
        { predicate = makeTruePredicate
        , substitution = []
        }
