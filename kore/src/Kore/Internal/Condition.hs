{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Internal.Condition (
    Condition,
    eraseConditionalTerm,
    top,
    bottom,
    topCondition,
    bottomCondition,
    fromPattern,
    Conditional.fromPredicate,
    Conditional.fromSingleSubstitution,
    Conditional.assign,
    Conditional.fromSubstitution,
    toPredicate,
    hasFreeVariable,
    Kore.Internal.Condition.mapVariables,
    fromNormalizationSimplified,

    -- * Re-exports
    Conditional (..),
    Conditional.andCondition,
) where

import ErrorContext
import Kore.Attribute.Pattern.FreeVariables (
    freeVariables,
    isFreeVariable,
 )
import Kore.Internal.Conditional (
    Condition,
    Conditional (..),
 )
import qualified Kore.Internal.Conditional as Conditional
import Kore.Internal.Predicate (
    Predicate,
 )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Substitution (
    Normalization (..),
 )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.Variable
import Kore.Syntax
import Prelude.Kore

-- | Erase the @Conditional@ 'term' to yield a 'Condition'.
eraseConditionalTerm ::
    Conditional variable child ->
    Condition variable
eraseConditionalTerm = Conditional.withoutTerm

top :: InternalVariable variable => Condition variable
top =
    Conditional
        { term = ()
        , predicate = Predicate.makeTruePredicate
        , substitution = mempty
        }

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

hasFreeVariable ::
    InternalVariable variable =>
    SomeVariableName variable ->
    Condition variable ->
    Bool
hasFreeVariable name = isFreeVariable name . freeVariables

{- | Extract the set of free set variables from a predicate and substitution.

    See also: 'Predicate.freeSetVariables'.
-}

{- | Transform a predicate and substitution into a predicate only.

@toPredicate@ is intended for generalizing the 'Predicate' and 'Substitution' of
a 'PredicateSubstition' into only a 'Predicate'.

See also: 'Substitution.toPredicate'.
-}
toPredicate ::
    InternalVariable variable =>
    Condition variable ->
    Predicate variable
toPredicate = from

mapVariables ::
    (InternalVariable variable1, InternalVariable variable2) =>
    AdjSomeVariableName (variable1 -> variable2) ->
    Condition variable1 ->
    Condition variable2
mapVariables = Conditional.mapVariables (\_ () -> ())

{- | Create a new 'Condition' from the 'Normalization' of a substitution.

The 'normalized' part becomes the normalized 'substitution', while the
'denormalized' part is converted into an ordinary 'predicate'.
-}
fromNormalizationSimplified ::
    HasCallStack =>
    InternalVariable variable =>
    Normalization variable ->
    Condition variable
fromNormalizationSimplified
    normalization@Normalization{normalized, denormalized} =
        predicate' <> substitution'
            & withErrorContext "while normalizing substitution" normalization
      where
        predicate' =
            Conditional.fromPredicate
                . Substitution.toPredicate
                $ Substitution.wrap denormalized
        substitution' =
            Conditional.fromSubstitution $
                Substitution.unsafeWrapFromAssignments normalized
