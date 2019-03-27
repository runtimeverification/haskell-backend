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

import           Kore.AST.Pure
import           Kore.IndexedModule.MetadataTools
import           Kore.Predicate.Predicate
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern, PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.Representation.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.Representation.OrOfExpandedPattern as OrOfExpandedPattern
                 ( isFalse, isTrue, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier,
                 SimplificationProof (SimplificationProof), Simplifier,
                 StepPatternSimplifier (..) )
import qualified Kore.Step.SMT.Evaluator as SmtEvaluator
import           Kore.Step.StepperAttributes
import           Kore.Unparser
import           Kore.Variables.Fresh
                 ( FreshVariable )

{- | Attempt to evaluate a predicate.

If the predicate is non-trivial (not @\\top{_}()@ or @\\bottom{_}()@),
@evaluate@ attempts to refute the predicate using an external SMT solver.

 -}
evaluate
    ::  forall level variable .
        ( FreshVariable variable
        , Given (MetadataTools level StepperAttributes)
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , Show (variable level)
        , ShowMetaOrObject variable
        , SortedVariable variable
        , Unparse (variable level)
        )
    => PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions in a pattern.
    -> Predicate level variable
    -- ^ The condition to be evaluated.
    -- TODO: Can't it happen that I also get a substitution when evaluating
    -- functions? See the Equals case.
    -> Simplifier
        (PredicateSubstitution level variable, SimplificationProof level)
evaluate
    substitutionSimplifier
    (StepPatternSimplifier simplifier)
    predicate
  = do
    (simplified, _proof) <-
        simplifier substitutionSimplifier (unwrapPredicate predicate)
    refute <-
        case () of
            _ | OrOfExpandedPattern.isTrue simplified -> return (Just True)
              | OrOfExpandedPattern.isFalse simplified -> return (Just False)
              | otherwise -> SmtEvaluator.decidePredicate predicate
    let simplified' =
            case refute of
                Just False -> ExpandedPattern.bottom
                Just True -> ExpandedPattern.top
                _ -> OrOfExpandedPattern.toExpandedPattern simplified
        (subst, _proof) = asPredicateSubstitution simplified'
    return (subst, SimplificationProof)

asPredicateSubstitution
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        )
    => ExpandedPattern level variable
    -> (PredicateSubstitution level variable, SimplificationProof level)
asPredicateSubstitution
    Predicated {term, predicate, substitution}
  =
    let
        andPatt = makeAndPredicate predicate (wrapPredicate term)
    in
        ( Predicated
            { term = ()
            , predicate = andPatt
            , substitution = substitution
            }
        , SimplificationProof
        )
