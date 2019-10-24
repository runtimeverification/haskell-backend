{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Internal.Predicate
    ( Predicate
    , isSimplified
    , markSimplified
    , eraseConditionalTerm
    , top
    , topTODO
    , bottom
    , topPredicate
    , bottomPredicate
    , fromPattern
    , Conditional.fromPredicate
    , Conditional.fromSingleSubstitution
    , Conditional.fromSubstitution
    , toPredicate
    , freeVariables
    , hasFreeVariable
    , Kore.Internal.Predicate.mapVariables
    -- * Re-exports
    , Conditional (..)
    , Conditional.andCondition
    ) where

import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    )
import Kore.Attribute.Pattern.FreeVariables
    ( isFreeVariable
    )
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Variable
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Syntax.Predicate
import Kore.Syntax
import Kore.Unparser
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )

-- | A predicate and substitution without an accompanying term.
type Predicate variable = Conditional variable ()

isSimplified :: Predicate variable -> Bool
isSimplified = Syntax.Predicate.isSimplified . Conditional.predicate

markSimplified :: Predicate variable -> Predicate variable
markSimplified conditional@Conditional { predicate } =
    conditional { predicate = Syntax.Predicate.markSimplified predicate }

-- | Erase the @Conditional@ 'term' to yield a 'Predicate'.
eraseConditionalTerm
    :: Conditional variable child
    -> Predicate variable
eraseConditionalTerm = Conditional.withoutTerm

top :: InternalVariable variable => Predicate variable
top =
    Conditional
        { term = ()
        , predicate = Syntax.Predicate.makeTruePredicate
        , substitution = mempty
        }

-- | A 'top' 'Predicate' for refactoring which should eventually be removed.
topTODO :: InternalVariable variable => Predicate variable
topTODO = top

bottom :: InternalVariable variable => Predicate variable
bottom =
    Conditional
        { term = ()
        , predicate = Syntax.Predicate.makeFalsePredicate
        , substitution = mempty
        }

topPredicate :: InternalVariable variable => Predicate variable
topPredicate = top

bottomPredicate :: InternalVariable variable => Predicate variable
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
    -> FreeVariables variable
freeVariables = Conditional.freeVariables (const mempty)

hasFreeVariable
    :: ( Ord variable
       , Show variable
       , Unparse variable
       , SortedVariable variable
       )
    => UnifiedVariable variable
    -> Predicate variable
    -> Bool
hasFreeVariable variable = isFreeVariable variable . freeVariables

{- | Extract the set of free set variables from a predicate and substitution.

    See also: 'Predicate.freeSetVariables'.
-}

{- | Transform a predicate and substitution into a predicate only.

@toPredicate@ is intended for generalizing the 'Predicate' and 'Substitution' of
a 'PredicateSubstition' into only a 'Predicate'.

See also: 'Syntax.Predicate.fromSubstitution'.

-}
toPredicate
    :: InternalVariable variable
    => Predicate variable
    -> Syntax.Predicate variable
toPredicate = Conditional.toPredicate

mapVariables
    :: (Ord variable1, Ord variable2)
    => (variable1 -> variable2)
    -> Predicate variable1
    -> Predicate variable2
mapVariables = Conditional.mapVariables (\_ () -> ())
