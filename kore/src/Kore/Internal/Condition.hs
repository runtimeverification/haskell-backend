{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Internal.Condition
    ( Condition
    , isSimplified
    , markSimplified
    , eraseConditionalTerm
    , top
    , topTODO
    , bottom
    , topCondition
    , bottomCondition
    , fromPattern
    , Conditional.fromPredicate
    , Conditional.fromSingleSubstitution
    , Conditional.fromSubstitution
    , toPredicate
    , freeVariables
    , hasFreeVariable
    , Kore.Internal.Condition.mapVariables
    , fromNormalizationSimplified
    -- * Re-exports
    , Conditional (..)
    , Conditional.andCondition
    ) where

import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables
    , isFreeVariable
    )
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
    ( isSimplified
    )
import Kore.Internal.Variable
import Kore.Predicate.Predicate
    ( Predicate
    )
import qualified Kore.Predicate.Predicate as Predicate
import Kore.Substitute
    ( SubstitutionVariable
    )
import Kore.Syntax
import Kore.Unification.Substitution
    ( Normalization (..)
    )
import qualified Kore.Unification.Substitution as Substitution
import Kore.Unparser
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )

-- | A predicate and substitution without an accompanying term.
type Condition variable = Conditional variable ()

isSimplified :: Condition variable -> Bool
isSimplified = Predicate.isSimplified . Conditional.predicate

markSimplified :: Condition variable -> Condition variable
markSimplified conditional@Conditional { predicate } =
    conditional { predicate = Predicate.markSimplified predicate }

-- | Erase the @Conditional@ 'term' to yield a 'Condition'.
eraseConditionalTerm
    :: Conditional variable child
    -> Condition variable
eraseConditionalTerm = Conditional.withoutTerm

top :: InternalVariable variable => Condition variable
top =
    Conditional
        { term = ()
        , predicate = Predicate.makeTruePredicate
        , substitution = mempty
        }

-- | A 'top' 'Condition' for refactoring which should eventually be removed.
topTODO :: InternalVariable variable => Condition variable
topTODO = top

bottom :: InternalVariable variable => Condition variable
bottom =
    Conditional
        { term = ()
        , predicate = Predicate.makeFalsePredicate
        , substitution = mempty
        }

topCondition :: InternalVariable variable => Condition variable
topCondition = top

bottomCondition :: InternalVariable variable => Condition variable
bottomCondition = bottom

{- | Extract the set of free variables from a predicate and substitution.

    See also: 'Predicate.freeVariables'.
-}

freeVariables
    :: ( Ord variable
       , Show variable
       , Unparse variable
       , SortedVariable variable
       )
    => Condition variable
    -> FreeVariables variable
freeVariables = Conditional.freeVariables (const mempty)

hasFreeVariable
    :: ( Ord variable
       , Show variable
       , Unparse variable
       , SortedVariable variable
       )
    => UnifiedVariable variable
    -> Condition variable
    -> Bool
hasFreeVariable variable = isFreeVariable variable . freeVariables

{- | Extract the set of free set variables from a predicate and substitution.

    See also: 'Predicate.freeSetVariables'.
-}

{- | Transform a predicate and substitution into a predicate only.

@toPredicate@ is intended for generalizing the 'Predicate' and 'Substitution' of
a 'PredicateSubstition' into only a 'Predicate'.

See also: 'Predicate.fromSubstitution'.

-}
toPredicate
    :: InternalVariable variable
    => Condition variable
    -> Predicate variable
toPredicate Conditional {predicate, substitution} =
    Predicate.makeAndPredicate
        predicate
        (Predicate.fromSubstitution substitution)

mapVariables
    :: (Ord variable1, Ord variable2)
    => (variable1 -> variable2)
    -> Condition variable1
    -> Condition variable2
mapVariables = Conditional.mapVariables (\_ () -> ())

{- | Create a new 'Condition' from the 'Normalization' of a substitution.

The 'normalized' part becomes the normalized 'substitution', while the
'denormalized' part is converted into an ordinary 'predicate'.

 -}
fromNormalizationSimplified
    :: SubstitutionVariable variable
    => Normalization variable
    -> Condition variable
fromNormalizationSimplified Normalization { normalized, denormalized } =
    predicate' <> substitution'
  where
    predicate' =
        Conditional.fromPredicate
        . markSimplifiedIfChildrenSimplified denormalized
        . Predicate.fromSubstitution
        $ Substitution.wrap denormalized
    substitution' =
        Conditional.fromSubstitution
        $ Substitution.unsafeWrap normalized
    markSimplifiedIfChildrenSimplified childrenList result =
        if childrenAreSimplified
            then Predicate.markSimplified result
            else result
      where
        childrenAreSimplified =
            all (TermLike.isSimplified) (map dropVariable childrenList)

        dropVariable
            :: (UnifiedVariable variable, TermLike variable)
            -> TermLike variable
        dropVariable = snd

