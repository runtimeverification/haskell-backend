{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Merging.Pattern
    ( mergeWithPredicateAssumesEvaluated
    , mergeWithPredicate
    ) where

import qualified Control.Monad.Trans.Class as Monad.Trans
import           Data.Reflection

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.Pattern
                 ( Conditional (..), Pattern, Predicate )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Condition.Evaluator as Predicate
                 ( evaluate )
import           Kore.Step.Simplification.Data
                 ( BranchT, PredicateSimplifier, Simplifier,
                 TermLikeSimplifier )
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
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        , Given (SmtMetadataTools StepperAttributes)
        )
    => SmtMetadataTools StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions in a pattern.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Predicate variable
    -- ^ Condition and substitution to add.
    -> Pattern variable
    -- ^ pattern to which the above should be added.
    -> BranchT Simplifier (Pattern variable)
mergeWithPredicate
    _tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
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
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            [pattPredicate, conditionToMerge]
            [pattSubstitution, substitutionToMerge]
    let Conditional { predicate = mergedCondition } = merged
    evaluatedCondition <- Monad.Trans.lift $
        Predicate.evaluate substitutionSimplifier simplifier mergedCondition
    let Conditional { substitution = mergedSubstitution } = merged
    mergeWithEvaluatedCondition
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        patt {substitution = mergedSubstitution}
        evaluatedCondition

mergeWithEvaluatedCondition
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Pattern variable
    -> Predicate variable
    -> BranchT Simplifier (Pattern variable)
mergeWithEvaluatedCondition
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    Conditional
        { term = pattTerm
        , substitution = pattSubstitution
        }  -- The predicate was already included in the Predicate
    Conditional
        { predicate = predPredicate, substitution = predSubstitution }
  = do
    merged <- mergePredicatesAndSubstitutions
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
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
