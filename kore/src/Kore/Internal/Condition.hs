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
    , bottom
    , topCondition
    , bottomCondition
    , fromPattern
    , Conditional.fromPredicate
    , Conditional.fromSingleSubstitution
    , Conditional.fromSubstitution
    , toPredicate
    , hasFreeVariable
    , coerceSort
    , conditionSort
    , Kore.Internal.Condition.mapVariables
    , fromNormalizationSimplified
    -- * Re-exports
    , Conditional (..)
    , Conditional.andCondition
    ) where

import qualified GHC.Stack as GHC

import Kore.Attribute.Pattern.FreeVariables
    ( freeVariables
    , isFreeVariable
    )
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Substitution
    ( Normalization (..)
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
    ( isSimplified
    )
import Kore.Internal.Variable
import Kore.Substitute
    ( SubstitutionVariable
    )
import Kore.Syntax
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
        , predicate = Predicate.makeTruePredicate_
        , substitution = mempty
        }

bottom :: InternalVariable variable => Condition variable
bottom =
    Conditional
        { term = ()
        , predicate = Predicate.makeFalsePredicate_
        , substitution = mempty
        }

topCondition :: InternalVariable variable => Condition variable
topCondition = top

bottomCondition :: InternalVariable variable => Condition variable
bottomCondition = bottom

hasFreeVariable
    :: InternalVariable variable
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

See also: 'Substitution.toPredicate'.

-}
toPredicate
    :: InternalVariable variable
    => Condition variable
    -> Predicate variable
toPredicate Conditional {predicate, substitution} =
    Predicate.makeAndPredicate
        predicate
        (Substitution.toPredicate substitution)

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
        . Substitution.toPredicate
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
            all TermLike.isSimplified (map dropVariable childrenList)

        dropVariable
            :: (UnifiedVariable variable, TermLike variable)
            -> TermLike variable
        dropVariable = snd

conditionSort :: Condition variable -> Sort
conditionSort Conditional {term = (), predicate} =
    Predicate.predicateSort predicate

coerceSort
    :: (GHC.HasCallStack, InternalVariable variable)
    => Sort -> Condition variable -> Condition variable
coerceSort
    sort
    Conditional {term = (), predicate, substitution}
  =
    Conditional
        { term = ()
        , predicate = Predicate.coerceSort sort predicate
        , substitution
        }
