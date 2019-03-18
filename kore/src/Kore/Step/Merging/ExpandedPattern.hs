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
import           Kore.Debug
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Condition.Evaluator as Predicate
                 ( evaluate )
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern, PredicateSubstitution, Predicated (..) )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier,
                 SimplificationProof (SimplificationProof), Simplifier,
                 StepPatternSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
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
        , Given (MetadataTools level StepperAttributes)
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions in a pattern.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> PredicateSubstitution level variable
    -- ^ Condition and substitution to add.
    -> ExpandedPattern level variable
    -- ^ pattern to which the above should be added.
    -> Simplifier (ExpandedPattern level variable, SimplificationProof level)
mergeWithPredicateSubstitution
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    Predicated
        { predicate = conditionToMerge
        , substitution = substitutionToMerge
        }
    patt@Predicated
        { predicate = pattPredicate
        , substitution = pattSubstitution
        }
  = do
    (   Predicated
            { predicate = mergedCondition
            , substitution = mergedSubstitution
            }
        , _proof ) <-
            traceNonErrorMonad D_ExpandedPattern_mergeWithPredicateSubstitution [debugArg "where" "mergePredicatesAndSubstitutions"]
            $ mergePredicatesAndSubstitutions
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                [pattPredicate, conditionToMerge]
                [pattSubstitution, substitutionToMerge]
    (evaluatedCondition, _) <-
        traceNonErrorMonad D_ExpandedPattern_mergeWithPredicateSubstitution [debugArg "where" "Predicate.evaluate"]
        $ Predicate.evaluate
            substitutionSimplifier simplifier mergedCondition
    traceNonErrorMonad D_ExpandedPattern_mergeWithPredicateSubstitution [debugArg "where" "mergeWithEvaluatedCondition"]
    $ mergeWithEvaluatedCondition
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
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> ExpandedPattern level variable
    -> PredicateSubstitution level variable
    -> Simplifier (ExpandedPattern level variable, SimplificationProof level)
mergeWithEvaluatedCondition
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    Predicated
        { term = pattTerm
        , substitution = pattSubstitution
        }  -- The predicate was already included in the PredicateSubstitution
    Predicated
        { predicate = predPredicate, substitution = predSubstitution }
  = do
    (   Predicated
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
        ( Predicated
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
    -> Predicated level variable term
    -> m (Predicated level variable term, SimplificationProof level)
mergeWithPredicateSubstitutionAssumesEvaluated
    (PredicateSubstitutionMerger substitutionMerger)
    Predicated
        { term = ()
        , predicate = predPredicate
        , substitution = predSubstitution
        }
    Predicated
        { term = pattTerm
        , predicate = pattPredicate
        , substitution = pattSubstitution
        }  -- The predicate was already included in the PredicateSubstitution
  = do
    Predicated
        { term = ()
        , predicate = mergedPredicate
        , substitution = mergedSubstitution
        } <-
            substitutionMerger
                [pattPredicate, predPredicate]
                [pattSubstitution, predSubstitution]
    return
        ( Predicated
            { term = pattTerm
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , SimplificationProof
        )
