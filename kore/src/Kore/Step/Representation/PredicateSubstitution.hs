{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Representation.PredicateSubstitution
    ( PredicateSubstitution
    , CommonPredicateSubstitution
    , erasePredicatedTerm
    , top
    , bottom
    , topPredicate
    , bottomPredicate
    , fromPurePattern
    , fromPredicate
    , toPredicate
    , freeVariables
    , Kore.Step.Representation.PredicateSubstitution.mapVariables
    -- * Re-exports
    , Predicated (..)
    ) where

import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import           Kore.AST.Pure
import           Kore.Predicate.Predicate
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Predicate
import           Kore.Step.Representation.Predicated
                 ( Predicated (..) )
import qualified Kore.Step.Representation.Predicated as Predicated
import           Kore.Unparser

-- | A predicate and substitution without an accompanying term.
type PredicateSubstitution level variable = Predicated level variable ()

-- | A 'PredicateSubstitution' of the 'Variable' type.
type CommonPredicateSubstitution level = PredicateSubstitution level Variable

-- | Erase the @Predicated@ 'term' to yield a 'PredicateSubstitution'.
erasePredicatedTerm
    :: Predicated level variable child
    -> PredicateSubstitution level variable
erasePredicatedTerm = Predicated.withoutTerm

top :: MetaOrObject level => PredicateSubstitution level variable
top =
    Predicated
        { term = ()
        , predicate = Predicate.makeTruePredicate
        , substitution = mempty
        }

bottom :: MetaOrObject level => PredicateSubstitution level variable
bottom =
    Predicated
        { term = ()
        , predicate = Predicate.makeFalsePredicate
        , substitution = mempty
        }

topPredicate :: MetaOrObject level => PredicateSubstitution level variable
topPredicate = top

bottomPredicate :: MetaOrObject level => PredicateSubstitution level variable
bottomPredicate = bottom

{- | Construct a 'PredicateSubstitution' from the given 'Predicate'.

The result has an empty 'Substitution'.

 -}
fromPredicate
    :: Predicate level variable
    -> PredicateSubstitution level variable
fromPredicate predicate =
    Predicated { term = (), predicate, substitution = mempty }

{- | Extract the set of free variables from a predicate and substitution.

    See also: 'Predicate.freeVariables'.
-}

freeVariables
    :: ( MetaOrObject level
       , Ord (variable level)
       , Show (variable level)
       , Unparse (variable level)
       , SortedVariable variable
       )
    => PredicateSubstitution level variable
    -> Set (variable level)
freeVariables = Predicated.freeVariables (const Set.empty)

{- | Transform a predicate and substitution into a predicate only.

@toPredicate@ is intended for generalizing the 'Predicate' and 'Substitution' of
a 'PredicateSubstition' into only a 'Predicate'.

See also: 'substitutionToPredicate'.

-}
toPredicate
    :: ( MetaOrObject level
       , SortedVariable variable
       , Ord (variable level)
       , Show (variable level)
       , Unparse (variable level)
       )
    => PredicateSubstitution level variable
    -> Predicate level variable
toPredicate = Predicated.toPredicate

mapVariables
    :: Ord (variable2 level)
    => (variable1 level -> variable2 level)
    -> PredicateSubstitution level variable1
    -> PredicateSubstitution level variable2
mapVariables = Predicated.mapVariables (\_ () -> ())
