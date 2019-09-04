{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Merging.Pattern
    ( mergeWithPredicateAssumesEvaluated
    , mergeWithPredicate
    ) where

import qualified Control.Monad.Trans.Class as Monad.Trans

import           Kore.Internal.Pattern
                 ( Conditional (..), Pattern, Predicate )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Logger
                 ( LogMessage, WithLog )
import qualified Kore.Step.Condition.Evaluator as Predicate
                 ( simplify )
import           Kore.Step.Simplification.Data as Simplifier
import           Kore.Step.Substitution
                 ( PredicateMerger (PredicateMerger),
                 mergePredicatesAndSubstitutions )
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.Unparser
import           Kore.Variables.Fresh

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
mergeWithPredicate
    Conditional
        { predicate = conditionToMerge
        , substitution = substitutionToMerge
        }
    patt@Conditional
        { predicate = pattPredicate
        , substitution = pattSubstitution
        }
  = do
    merged <-
        mergePredicatesAndSubstitutions
            [pattPredicate, conditionToMerge]
            [pattSubstitution, substitutionToMerge]
    let Conditional { predicate = mergedCondition } = merged
    evaluatedCondition <- Monad.Trans.lift $ Predicate.simplify mergedCondition
    let Conditional { substitution = mergedSubstitution } = merged
    mergeWithEvaluatedCondition
        patt {substitution = mergedSubstitution}
        evaluatedCondition

mergeWithEvaluatedCondition
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Pattern variable
    -> Predicate variable
    -> BranchT simplifier (Pattern variable)
mergeWithEvaluatedCondition
    Conditional
        { term = pattTerm
        , substitution = pattSubstitution
        }  -- The predicate was already included in the Predicate
    Conditional
        { predicate = predPredicate, substitution = predSubstitution }
  = do
    merged <-
        mergePredicatesAndSubstitutions
            [predPredicate]
            [pattSubstitution, predSubstitution]
    return $ Pattern.withCondition pattTerm merged

{-| Ands the given predicate/substitution with the given pattern.

Assumes that the initial patterns are simplified, so it does not attempt
to re-simplify them.
-}
mergeWithPredicateAssumesEvaluated
    ::  ( FreshVariable variable
        , Monad m
        , Ord variable
        , Show variable
        , SortedVariable variable
        , Unparse variable
        )
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
