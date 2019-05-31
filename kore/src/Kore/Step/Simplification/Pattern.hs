{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.Pattern
    ( simplify
    , simplifyPredicate
    ) where

import qualified Control.Monad.Trans.Class as Monad.Trans
import           Data.Reflection

import qualified Kore.Internal.MultiOr as MultiOr
import           Kore.Internal.OrPattern
                 ( OrPattern )
import           Kore.Internal.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Step.Condition.Evaluator as Predicate
                 ( evaluate )
import qualified Kore.Step.Merging.Pattern as Pattern
import           Kore.Step.Simplification.Data as Simplifier
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )
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
    => Pattern variable
    -> Simplifier (OrPattern variable)
simplify Conditional {term, predicate, substitution} = do
    termSimplifier <- Simplifier.askSimplifierTermLike
    substitutionSimplifier <- Simplifier.askSimplifierPredicate
    axiomIdToSimplifier <- Simplifier.askSimplifierAxioms
    let simplifyTerm' = simplifyTerm termSimplifier substitutionSimplifier
    simplifiedTerm <- simplifyTerm' term
    orPatterns <- BranchT.gather
        (traverse
            (Pattern.mergeWithPredicate
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
        )
    return (MultiOr.mergeAll orPatterns)

{-| Simplifies the predicate inside an 'Pattern'.
-}
simplifyPredicate
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions in a pattern.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Pattern variable
    -- ^ The condition to be evaluated.
    -> BranchT Simplifier (Pattern variable)
simplifyPredicate
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    Conditional {term, predicate, substitution}
  = do
    tools <- Simplifier.askMetadataTools
    evaluated <-
        give tools $ Monad.Trans.lift
        $ Predicate.evaluate
            substitutionSimplifier
            simplifier
            predicate
    let Conditional { predicate = evaluatedPredicate } = evaluated
        Conditional { substitution = evaluatedSubstitution } = evaluated
    merged <-
        mergePredicatesAndSubstitutions
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            [evaluatedPredicate]
            [substitution, evaluatedSubstitution]
    -- TODO(virgil): Do I need to re-evaluate the predicate?
    return $ Pattern.withCondition term merged
