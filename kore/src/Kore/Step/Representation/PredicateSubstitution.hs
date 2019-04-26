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
    , Predicated.fromPredicate
    , Predicated.fromSubstitution
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
    :: Predicated Object variable child
    -> PredicateSubstitution Object variable
erasePredicatedTerm = Predicated.withoutTerm

top
    ::  ( MetaOrObject Object
        , Ord (variable Object)
        )
    => PredicateSubstitution Object variable
top =
    Predicated
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
    Predicated
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
freeVariables = Predicated.freeVariables (const Set.empty)

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
toPredicate = Predicated.toPredicate

mapVariables
    :: Ord (variable2 Object)
    => (variable1 Object -> variable2 Object)
    -> PredicateSubstitution Object variable1
    -> PredicateSubstitution Object variable2
mapVariables = Predicated.mapVariables (\_ () -> ())
