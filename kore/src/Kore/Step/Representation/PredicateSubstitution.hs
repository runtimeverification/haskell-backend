{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Representation.PredicateSubstitution
    ( PredicateSubstitution
    , CommonPredicateSubstitution
    , eraseConditionalTerm
    , top
    , bottom
    , topPredicate
    , bottomPredicate
    , fromPurePattern
    , Conditional.fromPredicate
    , Conditional.fromSubstitution
    , toPredicate
    , freeVariables
    , Kore.Step.Representation.PredicateSubstitution.mapVariables
    -- * Re-exports
    , Conditional (..)
    ) where

import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import           Kore.AST.Pure
import           Kore.Predicate.Predicate
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Conditional
                 ( Conditional (..) )
import qualified Kore.Step.Conditional as Conditional
import           Kore.Unparser

-- | A predicate and substitution without an accompanying term.
type PredicateSubstitution level variable = Conditional level variable ()

-- | A 'PredicateSubstitution' of the 'Variable' type.
type CommonPredicateSubstitution level = PredicateSubstitution level Variable

-- | Erase the @Conditional@ 'term' to yield a 'PredicateSubstitution'.
eraseConditionalTerm
    :: Conditional Object variable child
    -> PredicateSubstitution Object variable
eraseConditionalTerm = Conditional.withoutTerm

top
    ::  ( MetaOrObject Object
        , Ord (variable Object)
        )
    => PredicateSubstitution Object variable
top =
    Conditional
        { term = ()
        , predicate = Predicate.makeTruePredicate
        , substitution = mempty
        }

bottom
    ::  ( MetaOrObject Object
        , Ord (variable Object)
        )
    => PredicateSubstitution Object variable
bottom =
    Conditional
        { term = ()
        , predicate = Predicate.makeFalsePredicate
        , substitution = mempty
        }

topPredicate
    ::  ( MetaOrObject Object
        , Ord (variable Object)
        )
    => PredicateSubstitution Object variable
topPredicate = top

bottomPredicate
    ::  ( MetaOrObject Object
        , Ord (variable Object)
        )
    => PredicateSubstitution Object variable
bottomPredicate = bottom

{- | Extract the set of free variables from a predicate and substitution.

    See also: 'Predicate.freeVariables'.
-}

freeVariables
    :: ( MetaOrObject Object
       , Ord (variable Object)
       , Show (variable Object)
       , Unparse (variable Object)
       , SortedVariable variable
       )
    => PredicateSubstitution Object variable
    -> Set (variable Object)
freeVariables = Conditional.freeVariables (const Set.empty)

{- | Transform a predicate and substitution into a predicate only.

@toPredicate@ is intended for generalizing the 'Predicate' and 'Substitution' of
a 'PredicateSubstition' into only a 'Predicate'.

See also: 'substitutionToPredicate'.

-}
toPredicate
    :: ( MetaOrObject Object
       , SortedVariable variable
       , Ord (variable Object)
       , Show (variable Object)
       , Unparse (variable Object)
       )
    => PredicateSubstitution Object variable
    -> Predicate variable
toPredicate = Conditional.toPredicate

mapVariables
    :: Ord (variable2 Object)
    => (variable1 Object -> variable2 Object)
    -> PredicateSubstitution Object variable1
    -> PredicateSubstitution Object variable2
mapVariables = Conditional.mapVariables (\_ () -> ())
