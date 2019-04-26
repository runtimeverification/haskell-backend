{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.Pattern
    ( simplify
    , simplifyPredicate
    ) where

import           Data.Reflection
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
import qualified Kore.Step.Merging.Pattern as Pattern
import qualified Kore.Step.Or as Or
import           Kore.Step.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( traverseWithPairs )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier, simplifyTerm )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Unparser
import           Kore.Variables.Fresh

{-| Simplifies an 'Pattern', returning an 'Or.Pattern'.
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
    => SmtMetadataTools StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions in patterns.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> Pattern level variable
    -> Simplifier
        ( Or.Pattern level variable
        , SimplificationProof level
        )
simplify
    tools
    substitutionSimplifier
    termSimplifier
    axiomIdToSimplifier
    Conditional {term, predicate, substitution}
  = do
    (simplifiedTerm, _) <- simplifyTerm' term
    (simplifiedPatt, _) <-
        MultiOr.traverseWithPairs
            (give tools $ Pattern.mergeWithPredicateSubstitution
                tools
                substitutionSimplifier
                termSimplifier
                axiomIdToSimplifier
                Conditional
                    { term = ()
                    , predicate
                    , substitution
                    }
            )
            simplifiedTerm
    return (simplifiedPatt, SimplificationProof)
  where
    simplifyTerm' = simplifyTerm termSimplifier substitutionSimplifier

{-| Simplifies the predicate inside an 'Pattern'.
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
    => SmtMetadataTools StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions in a pattern.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> Pattern level variable
    -- ^ The condition to be evaluated.
    -> Simplifier (Pattern level variable, SimplificationProof level)
simplifyPredicate
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    Conditional {term, predicate, substitution}
  = do
    (evaluated, _proof) <-
        give tools
            $ Predicate.evaluate
                substitutionSimplifier
                simplifier
                predicate
    let Conditional { predicate = evaluatedPredicate } = evaluated
        Conditional { substitution = evaluatedSubstitution } = evaluated
    (merged, _proof) <-
        mergePredicatesAndSubstitutions
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            [evaluatedPredicate]
            [substitution, evaluatedSubstitution]
    let Conditional { predicate = mergedPredicate } = merged
        Conditional { substitution = mergedSubstitution } = merged
    -- TODO(virgil): Do I need to re-evaluate the predicate?
    return
        ( Conditional
            { term = term
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , SimplificationProof
        )
