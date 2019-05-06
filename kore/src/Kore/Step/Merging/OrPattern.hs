{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Merging.OrPattern
    ( mergeWithPredicate
    , mergeWithPredicateAssumesEvaluated
    ) where

import Data.Reflection

import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( SmtMetadataTools )
import           Kore.Internal.MultiOr
                 ( MultiOr )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import           Kore.Internal.Pattern
                 ( Conditional, Predicate )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Merging.Pattern as Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier )
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
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
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
    -- ^ Predicate to add.
    -> OrPattern variable
    -- ^ Pattern to which the condition should be added.
    -> Simplifier (OrPattern variable)
mergeWithPredicate
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    toMerge
    patt
  =
    traverse
        (give tools $ Pattern.mergeWithPredicate
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            toMerge
        )
        patt

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
mergeWithPredicateAssumesEvaluated substitutionMerger toMerge =
    traverse
        (Pattern.mergeWithPredicateAssumesEvaluated substitutionMerger toMerge)
