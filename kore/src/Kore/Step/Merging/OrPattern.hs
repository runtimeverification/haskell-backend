{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Merging.OrPattern
    ( mergeWithPredicate
    , mergeWithPredicateAssumesEvaluated
    ) where

import           Kore.Internal.MultiOr
                 ( MultiOr )
import qualified Kore.Internal.MultiOr as MultiOr
                 ( mergeAll )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import           Kore.Internal.Pattern
                 ( Conditional, Predicate )
import           Kore.Logger
                 ( LogMessage, WithLog )
import qualified Kore.Step.Merging.Pattern as Pattern
import           Kore.Step.Simplification.Data
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )
import           Kore.Step.Substitution
                 ( PredicateMerger )
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.TopBottom
                 ( TopBottom )
import           Kore.Unparser
import           Kore.Variables.Fresh

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
    ::  ( FreshVariable variable
        , Monad m
        , Ord term
        , Show variable
        , SortedVariable variable
        , TopBottom term
        , Unparse variable
        )
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
