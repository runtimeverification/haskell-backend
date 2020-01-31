{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Internal.Condition
    ( Condition
    , isSimplified
    , simplifiedAttribute
    , markPredicateSimplified
    , setPredicateSimplified
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

import Prelude.Kore

import Kore.Attribute.Pattern.FreeVariables
    ( freeVariables
    , isFreeVariable
    )
import qualified Kore.Attribute.Pattern.Simplified as Attribute
    ( Simplified
    )
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition
    ( Representation
    )
import Kore.Internal.Substitution
    ( Normalization (..)
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
    ( simplifiedAttribute
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

isSimplified :: SideCondition.Representation -> Condition variable -> Bool
isSimplified sideCondition Conditional {term = (), predicate, substitution} =
    Predicate.isSimplified sideCondition predicate
    && Substitution.isSimplified sideCondition substitution

simplifiedAttribute :: Condition variable -> Attribute.Simplified
simplifiedAttribute Conditional {term = (), predicate, substitution} =
    Predicate.simplifiedAttribute predicate
    <> Substitution.simplifiedAttribute substitution

{-| Marks the condition's predicate as being simplified.

Since the substitution is usually simplified, this usually marks the entire
condition as simplified. Note however, that the way in which the condition
is simplified is a combination of the predicate and substitution
simplifications. As an example, if the predicate is fully simplified,
while the substitution is simplified only for a certain side condition,
the entire condition is simplified only for that side condition.
-}
markPredicateSimplified
    :: (HasCallStack, InternalVariable variable)
    => Condition variable -> Condition variable
markPredicateSimplified conditional@Conditional { predicate } =
    conditional { predicate = Predicate.markSimplified predicate }

{-| Sets the simplified attribute for a condition's predicate.

See 'markPredicateSimplified' for details.
-}
setPredicateSimplified
    :: InternalVariable variable
    => Attribute.Simplified -> Condition variable -> Condition variable
setPredicateSimplified simplified conditional@Conditional { predicate } =
    conditional { predicate = Predicate.setSimplified simplified predicate }

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
        Predicate.setSimplified childrenSimplified result
      where
        childrenSimplified =
            foldMap (TermLike.simplifiedAttribute . dropVariable) childrenList

        dropVariable
            :: (UnifiedVariable variable, TermLike variable)
            -> TermLike variable
        dropVariable = snd

conditionSort :: Condition variable -> Sort
conditionSort Conditional {term = (), predicate} =
    Predicate.predicateSort predicate

coerceSort
    :: (HasCallStack, InternalVariable variable)
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
