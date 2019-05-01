{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Predicate
    ( Predicate
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
    , Kore.Step.Predicate.mapVariables
    -- * Re-exports
    , Conditional (..)
    ) where

import           Data.Set
                 ( Set )
import qualified Data.Set as Set

import           Kore.AST.Pure
import qualified Kore.Predicate.Predicate as Syntax
                 ( Predicate )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import           Kore.Step.Conditional
                 ( Conditional (..) )
import qualified Kore.Step.Conditional as Conditional
import           Kore.Unparser

-- | A predicate and substitution without an accompanying term.
type Predicate variable = Conditional variable ()

-- | Erase the @Conditional@ 'term' to yield a 'Predicate'.
eraseConditionalTerm
    :: Conditional variable child
    -> Predicate variable
eraseConditionalTerm = Conditional.withoutTerm

top :: Ord variable => Predicate variable
top =
    Conditional
        { term = ()
        , predicate = Syntax.Predicate.makeTruePredicate
        , substitution = mempty
        }

bottom :: Ord variable => Predicate variable
bottom =
    Conditional
        { term = ()
        , predicate = Syntax.Predicate.makeFalsePredicate
        , substitution = mempty
        }

topPredicate :: Ord variable => Predicate variable
topPredicate = top

bottomPredicate
    :: Ord variable
    => Predicate variable
bottomPredicate = bottom

{- | Extract the set of free variables from a predicate and substitution.

    See also: 'Predicate.freeVariables'.
-}

freeVariables
    :: ( Ord variable
       , Show variable
       , Unparse variable
       , SortedVariable variable
       )
    => Predicate variable
    -> Set variable
freeVariables = Conditional.freeVariables (const Set.empty)

{- | Transform a predicate and substitution into a predicate only.

@toPredicate@ is intended for generalizing the 'Predicate' and 'Substitution' of
a 'PredicateSubstition' into only a 'Predicate'.

See also: 'substitutionToPredicate'.

-}
toPredicate
    :: ( SortedVariable variable
       , Ord variable
       , Show variable
       , Unparse variable
       )
    => Predicate variable
    -> Syntax.Predicate variable
toPredicate = Conditional.toPredicate

mapVariables
    :: Ord variable2
    => (variable1 -> variable2)
    -> Predicate variable1
    -> Predicate variable2
mapVariables = Conditional.mapVariables (\_ () -> ())
