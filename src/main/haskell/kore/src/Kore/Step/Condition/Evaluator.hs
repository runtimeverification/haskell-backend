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

import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SymbolOrAliasSorts )
import           Kore.Predicate.Predicate
import           Kore.SMT.SMT
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( isFalse, isTrue, toExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier,
                 PureMLPatternSimplifier (..),
                 SimplificationProof (SimplificationProof), Simplifier )
import           Kore.Step.StepperAttributes

{- | 'evaluate' attempts to evaluate a Kore predicate.

If the predicate is non-trivial (not @\\top{_}()@ or @\\bottom{_}()@),
@evaluate@ attempts to refute the predicate using an external SMT solver.

 -}
evaluate
    ::  forall level variable .
        ( MetaOrObject level
        , SortedVariable variable
        , Eq (variable level)
        , Ord (variable level)
        , Show (variable level)
        , Given (MetadataTools level StepperAttributes)
        )
    => PredicateSubstitutionSimplifier level Simplifier
    -> PureMLPatternSimplifier level variable
    -- ^ Evaluates functions in a pattern.
    -> Predicate level variable
    -- ^ The condition to be evaluated.
    -- TODO: Can't it happen that I also get a substitution when evaluating
    -- functions? See the Equals case.
    -> Simplifier
        (PredicateSubstitution level variable, SimplificationProof level)
evaluate
    substitutionSimplifier
    (PureMLPatternSimplifier simplifier)
    predicate
  = give symbolOrAliasSorts $ do
    (simplified, _proof) <-
        simplifier substitutionSimplifier (unwrapPredicate predicate)
    refute <-
        case () of
            _ | OrOfExpandedPattern.isTrue simplified -> return (Just True)
              | OrOfExpandedPattern.isFalse simplified -> return (Just False)
              | otherwise -> refutePredicate predicate
    let simplified' =
            case refute of
                Just False -> ExpandedPattern.bottom
                _ -> OrOfExpandedPattern.toExpandedPattern simplified
        (subst, _proof) = asPredicateSubstitution simplified'
    return (subst, SimplificationProof)
  where
    MetadataTools { symbolOrAliasSorts } =
        given :: MetadataTools level StepperAttributes

asPredicateSubstitution
    ::  ( MetaOrObject level
        , Given (SymbolOrAliasSorts level)
        , SortedVariable variable
        , Eq (variable level)
        , Show (variable level)
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
