{-|
Module      : Kore.Step.Simplification.ExpandedPattern
Description : Tools for ExpandedPattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.ExpandedPattern
    ( simplify
    , simplifyPredicate
    ) where

import           Data.Reflection
import           Kore.AST.Common
                 ( SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import qualified Kore.Step.Condition.Evaluator as Predicate
                 ( evaluate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, Predicated (..) )
import           Kore.Step.Function.Data
                 ( BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Merging.ExpandedPattern as ExpandedPattern
                 ( mergeWithPredicateSubstitution )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( traverseWithPairs )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (..),
                 StepPatternSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Unparser
import           Kore.Variables.Fresh

{-| Simplifies an 'ExpandedPattern', returning an 'OrOfExpandedPattern'.
-}
simplify
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
    -- ^ Evaluates functions in patterns.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> ExpandedPattern level variable
    -> Simplifier
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    tools
    substitutionSimplifier
    wrappedSimplifier@(StepPatternSimplifier simplifier)
    axiomIdToSimplifier
    Predicated {term, predicate, substitution}
  = do
    (simplifiedTerm, _)
        <- simplifier substitutionSimplifier term
    (simplifiedPatt, _) <-
        OrOfExpandedPattern.traverseWithPairs
            (give tools $ ExpandedPattern.mergeWithPredicateSubstitution
                tools
                substitutionSimplifier
                wrappedSimplifier
                axiomIdToSimplifier
                Predicated
                    { term = ()
                    , predicate
                    , substitution
                    }
            )
            simplifiedTerm
    return (simplifiedPatt, SimplificationProof)

{-| Simplifies the predicate inside an 'ExpandedPattern'.
-}
simplifyPredicate
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
    -> ExpandedPattern level variable
    -- ^ The condition to be evaluated.
    -> Simplifier (ExpandedPattern level variable, SimplificationProof level)
simplifyPredicate
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    Predicated {term, predicate, substitution}
  = do
    (evaluated, _proof) <-
        give tools
            $ Predicate.evaluate
                substitutionSimplifier
                simplifier
                predicate
    let Predicated { predicate = evaluatedPredicate } = evaluated
        Predicated { substitution = evaluatedSubstitution } = evaluated
    (merged, _proof) <-
        mergePredicatesAndSubstitutions
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            [evaluatedPredicate]
            [substitution, evaluatedSubstitution]
    let Predicated { predicate = mergedPredicate } = merged
        Predicated { substitution = mergedSubstitution } = merged
    -- TODO(virgil): Do I need to re-evaluate the predicate?
    return
        ( Predicated
            { term = term
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , SimplificationProof
        )
