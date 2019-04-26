{-|
Module      : Kore.Step.Condition.Evaluator
Description : Evaluates conditions.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Condition.Evaluator
    ( evaluate
    ) where

import Data.Reflection

import           Kore.Attribute.Symbol
import           Kore.IndexedModule.MetadataTools
import           Kore.Predicate.Predicate
import qualified Kore.Step.Or as Or
import           Kore.Step.Pattern as Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier,
                 SimplificationProof (SimplificationProof), Simplifier,
                 StepPatternSimplifier, simplifyTerm )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{- | Attempt to evaluate a predicate.

If the predicate is non-trivial (not @\\top{_}()@ or @\\bottom{_}()@),
@evaluate@ attempts to refute the predicate using an external SMT solver.

 -}
evaluate
    ::  forall variable .
        ( FreshVariable variable
        , SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        , Given (SmtMetadataTools StepperAttributes)
        )
    => PredicateSubstitutionSimplifier Object
    -> StepPatternSimplifier Object
    -- ^ Evaluates functions in a pattern.
    -> Predicate variable
    -- ^ The condition to be evaluated.
    -- TODO: Can't it happen that I also get a substitution when evaluating
    -- functions? See the Equals case.
    -> Simplifier
        (PredicateSubstitution Object variable, SimplificationProof Object)
evaluate
    substitutionSimplifier
    termSimplifier
    predicate
  = do
    (simplified, _proof) <- simplifyTerm' (unwrapPredicate predicate)
    refute <-
        case () of
            _ | Or.isTrue simplified -> return (Just True)
              | Or.isFalse simplified -> return (Just False)
              | otherwise -> SMT.Evaluator.decidePredicate predicate
    let simplified' =
            case refute of
                Just False -> Pattern.bottom
                Just True -> Pattern.top
                _ -> Or.toExpandedPattern simplified
        (subst, _proof) = asPredicateSubstitution simplified'
    return (subst, SimplificationProof)
  where
    simplifyTerm' = simplifyTerm termSimplifier substitutionSimplifier

asPredicateSubstitution
    ::  ( SortedVariable variable
        , Ord (variable Object)
        , Show (variable Object)
        , Unparse (variable Object)
        )
    => Pattern Object variable
    -> (PredicateSubstitution Object variable, SimplificationProof Object)
asPredicateSubstitution
    Conditional {term, predicate, substitution}
  =
    let
        andPatt = makeAndPredicate predicate (wrapPredicate term)
    in
        ( Conditional
            { term = ()
            , predicate = andPatt
            , substitution = substitution
            }
        , SimplificationProof
        )
