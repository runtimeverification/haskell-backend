{-|
Module      : Kore.Step.Merging.OrOfExpandedPattern
Description : Tools for merging OrOfExpandedPatterns with various stuff.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Merging.OrOfExpandedPattern
    ( mergeWithPredicateSubstitution
    , mergeWithPredicateSubstitutionAssumesEvaluated
    ) where

import Data.Reflection

import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Merging.ExpandedPattern as ExpandedPattern
                 ( mergeWithPredicateSubstitution,
                 mergeWithPredicateSubstitutionAssumesEvaluated )
import           Kore.Step.Representation.ExpandedPattern
                 ( PredicateSubstitution, Predicated )
import           Kore.Step.Representation.MultiOr
                 ( MultiOr )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( traverseWithPairs )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier )
import           Kore.Step.Substitution
                 ( PredicateSubstitutionMerger )
import           Kore.TopBottom
                 ( TopBottom )
import           Kore.Unparser
import           Kore.Variables.Fresh

{-| 'mergeWithPredicateSubstitution' ands the given predicate/substitution
to the given Or.
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
    -- ^ PredicateSubstitution to add.
    -> OrOfExpandedPattern level variable
    -- ^ Pattern to which the condition should be added.
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
mergeWithPredicateSubstitution
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    toMerge
    patt
  = do
    (evaluated, _proofs) <-
        MultiOr.traverseWithPairs
            (give tools $ ExpandedPattern.mergeWithPredicateSubstitution
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                toMerge
            )
            patt
    return (evaluated, SimplificationProof)

{-| Ands the given predicate/substitution with the given 'MultiOr'.

Assumes that the initial patterns are simplified, so it does not attempt
to re-simplify them.
-}
mergeWithPredicateSubstitutionAssumesEvaluated
    ::  ( FreshVariable variable
        , MetaOrObject level
        , Monad m
        , Ord term
        , Ord (variable level)
        , OrdMetaOrObject variable
        , Show (variable level)
        , ShowMetaOrObject variable
        , SortedVariable variable
        , TopBottom term
        , Unparse (variable level)
        )
    => PredicateSubstitutionMerger level variable m
    -> PredicateSubstitution level variable
    -- ^ PredicateSubstitution to add.
    -> MultiOr (Predicated level variable term)
    -- ^ Pattern to which the condition should be added.
    -> m
        (MultiOr (Predicated level variable term), SimplificationProof level)
mergeWithPredicateSubstitutionAssumesEvaluated
    substitutionMerger
    toMerge
    patt
  = do
    (evaluated, _proofs) <-
        MultiOr.traverseWithPairs
            (ExpandedPattern.mergeWithPredicateSubstitutionAssumesEvaluated
                    substitutionMerger
                    toMerge
            )
            patt
    return (evaluated, SimplificationProof)
