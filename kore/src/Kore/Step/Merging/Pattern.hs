{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Merging.Pattern
    ( mergeWithPredicateAssumesEvaluated
    , mergeWithPredicate
    ) where

import Branch
    ( BranchT
    )
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    , Predicate
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Logger
    ( LogMessage
    , WithLog
    )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Substitution
    ( PredicateMerger (PredicateMerger)
    )

{-| 'mergeWithPredicate' ands the given predicate-substitution
with the given pattern.
-}
mergeWithPredicate
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Predicate variable
    -- ^ Condition and substitution to add.
    -> Pattern variable
    -- ^ pattern to which the above should be added.
    -> BranchT simplifier (Pattern variable)
mergeWithPredicate condition' pattern' =
    simplifyPredicate $ Pattern.andCondition pattern' condition'

{-| Ands the given predicate/substitution with the given pattern.

Assumes that the initial patterns are simplified, so it does not attempt
to re-simplify them.
-}
mergeWithPredicateAssumesEvaluated
    :: (SimplifierVariable variable, Monad m)
    => PredicateMerger variable m
    -> Predicate variable
    -> Conditional variable term
    -> m (Conditional variable term)
mergeWithPredicateAssumesEvaluated
    (PredicateMerger substitutionMerger)
    Conditional
        { term = ()
        , predicate = predPredicate
        , substitution = predSubstitution
        }
    Conditional
        { term
        , predicate = pattPredicate
        , substitution = pattSubstitution
        }  -- The predicate was already included in the Predicate
  = do
    merged <-
        substitutionMerger
            [pattPredicate, predPredicate]
            [pattSubstitution, predSubstitution]
    return (Pattern.withCondition term merged)
