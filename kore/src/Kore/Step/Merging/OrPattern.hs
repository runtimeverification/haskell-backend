{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Merging.OrPattern
    ( mergeWithPredicate
    , mergeWithPredicateAssumesEvaluated
    ) where

import qualified Branch as BranchT
import Kore.Internal.MultiOr
    ( MultiOr
    )
import qualified Kore.Internal.MultiOr as MultiOr
    ( mergeAll
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern
    ( Conditional
    , Predicate
    )
import Kore.Logger
    ( LogMessage
    , WithLog
    )
import qualified Kore.Step.Merging.Pattern as Pattern
import Kore.Step.Simplification.Simplify
import Kore.Step.Substitution
    ( PredicateMerger
    )
import Kore.TopBottom
    ( TopBottom
    )

{-| 'mergeWithPredicate' ands the given predicate/substitution
to the given OrPattern.
-}
mergeWithPredicate
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Predicate variable
    -- ^ Predicate to add.
    -> OrPattern variable
    -- ^ Pattern to which the condition should be added.
    -> simplifier (OrPattern variable)
mergeWithPredicate toMerge patt = do
    patterns <-
        BranchT.gather $ traverse (Pattern.mergeWithPredicate toMerge) patt
    return (MultiOr.mergeAll patterns)

{-| Ands the given predicate/substitution with the given 'MultiOr'.

Assumes that the initial patterns are simplified, so it does not attempt
to re-simplify them.
-}
mergeWithPredicateAssumesEvaluated
    :: (SimplifierVariable variable, Monad m, TopBottom term)
    => PredicateMerger variable m
    -> Predicate variable
    -- ^ Predicate to add.
    -> MultiOr (Conditional variable term)
    -- ^ Pattern to which the condition should be added.
    -> m (MultiOr (Conditional variable term))
mergeWithPredicateAssumesEvaluated substitutionMerger toMerge patt =
    traverse
        (Pattern.mergeWithPredicateAssumesEvaluated substitutionMerger toMerge)
        patt
