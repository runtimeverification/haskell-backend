{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.Pattern
    ( simplify
    , simplifyPredicate
    ) where

import           Data.Reflection
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
import           Kore.Step.OrPattern
                 ( OrPattern )
import           Kore.Step.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( traverseWithPairs )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, SimplificationProof (..), Simplifier,
                 TermLikeSimplifier, simplifyTerm )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Syntax.Variable
                 ( SortedVariable )
import           Kore.Unparser
import           Kore.Variables.Fresh

{-| Simplifies an 'Pattern', returning an 'OrPattern'.
-}
simplify
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier Object
    -- ^ Evaluates functions in patterns.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from axiom IDs to axiom evaluators
    -> Pattern variable
    -> Simplifier
        ( OrPattern variable
        , SimplificationProof Object
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
            (give tools $ Pattern.mergeWithPredicate
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
    -> TermLikeSimplifier Object
    -- ^ Evaluates functions in a pattern.
    -> BuiltinAndAxiomSimplifierMap Object
    -- ^ Map from axiom IDs to axiom evaluators
    -> Pattern variable
    -- ^ The condition to be evaluated.
    -> Simplifier (Pattern variable, SimplificationProof Object)
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
