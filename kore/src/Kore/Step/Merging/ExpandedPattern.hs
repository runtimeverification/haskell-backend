{-|
Module      : Kore.Step.Merging.ExpandedPattern
Description : Tools for merging ExpandedPatterns with various stuff.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Merging.ExpandedPattern
    ( mergeWithPredicateSubstitutionAssumesEvaluated
    , mergeWithPredicateSubstitution
    ) where

import Data.Reflection

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Condition.Evaluator as Predicate
                 ( evaluate )
import           Kore.Step.Pattern
                 ( Conditional (..), Pattern, PredicateSubstitution )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier,
                 SimplificationProof (SimplificationProof), Simplifier,
                 StepPatternSimplifier )
import           Kore.Step.Substitution
                 ( PredicateSubstitutionMerger (PredicateSubstitutionMerger),
                 mergePredicatesAndSubstitutions )
import           Kore.Unparser
import           Kore.Variables.Fresh

{-| 'mergeWithPredicateSubstitution' ands the given predicate-substitution
with the given pattern.
-}
mergeWithPredicateSubstitution
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        , Given (SmtMetadataTools StepperAttributes)
        )
    => SmtMetadataTools StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions in a pattern.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> PredicateSubstitution level variable
    -- ^ Condition and substitution to add.
    -> Pattern level variable
    -- ^ pattern to which the above should be added.
    -> Simplifier (Pattern level variable, SimplificationProof level)
mergeWithPredicateSubstitution
    tools
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
    (   Conditional
            { predicate = mergedCondition
            , substitution = mergedSubstitution
            }
        , _proof ) <-
            mergePredicatesAndSubstitutions
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                [pattPredicate, conditionToMerge]
                [pattSubstitution, substitutionToMerge]
    (evaluatedCondition, _) <-
        Predicate.evaluate
            substitutionSimplifier simplifier mergedCondition
    mergeWithEvaluatedCondition
        tools
        substitutionSimplifier
        simplifier
        axiomIdToSimplifier
        patt {substitution = mergedSubstitution}
        evaluatedCondition

mergeWithEvaluatedCondition
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> Pattern level variable
    -> PredicateSubstitution level variable
    -> Simplifier (Pattern level variable, SimplificationProof level)
mergeWithEvaluatedCondition
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    Conditional
        { term = pattTerm
        , substitution = pattSubstitution
        }  -- The predicate was already included in the PredicateSubstitution
    Conditional
        { predicate = predPredicate, substitution = predSubstitution }
  = do
    (   Conditional
            { predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , _proof
        ) <- mergePredicatesAndSubstitutions
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            [predPredicate]
            [pattSubstitution, predSubstitution]
    return
        ( Conditional
            { term = pattTerm
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , SimplificationProof
        )

{-| Ands the given predicate/substitution with the given pattern.

Assumes that the initial patterns are simplified, so it does not attempt
to re-simplify them.
-}
mergeWithPredicateSubstitutionAssumesEvaluated
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Monad m
        , Ord (variable level)
        , OrdMetaOrObject variable
        , Show (variable level)
        , ShowMetaOrObject variable
        , SortedVariable variable
        , Unparse (variable level)
        )
    => PredicateSubstitutionMerger level variable m
    -> PredicateSubstitution level variable
    -> Conditional level variable term
    -> m (Conditional level variable term, SimplificationProof level)
mergeWithPredicateSubstitutionAssumesEvaluated
    (PredicateSubstitutionMerger substitutionMerger)
    Conditional
        { term = ()
        , predicate = predPredicate
        , substitution = predSubstitution
        }
    Conditional
        { term = pattTerm
        , predicate = pattPredicate
        , substitution = pattSubstitution
        }  -- The predicate was already included in the PredicateSubstitution
  = do
    Conditional
        { term = ()
        , predicate = mergedPredicate
        , substitution = mergedSubstitution
        } <-
            substitutionMerger
                [pattPredicate, predPredicate]
                [pattSubstitution, predSubstitution]
    return
        ( Conditional
            { term = pattTerm
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , SimplificationProof
        )
