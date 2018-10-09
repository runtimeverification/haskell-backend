{-|
Module      : Kore.Step.Function.Evaluator
Description : Evaluates functions in a pattern.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Function.Evaluator
    ( evaluateApplication
    ) where

import           Control.Exception
                 ( assert )
import           Data.List
                 ( nub, partition )
import qualified Data.Map as Map

import           Kore.AST.Common
                 ( Application (..), Id (..), Pattern (..), PureMLPattern,
                 Sort, SortedVariable, SymbolOrAlias (..) )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( asPurePattern )
import           Kore.ASTUtils.SmartPatterns
                 ( pattern App_ )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( PredicateSubstitution, Predicated (..) )
import           Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator (..) )
import           Kore.Step.Function.Data as AttemptedFunction
                 ( AttemptedFunction (..) )
import qualified Kore.Step.Merging.OrOfExpandedPattern as OrOfExpandedPattern
                 ( mergeWithPredicateSubstitution )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( isFalse, make, merge )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier (..), SimplificationProof (..),
                 Simplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Fresh

{-| 'evaluateApplication' - evaluates functions on an application pattern.
-}
evaluateApplication
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , FreshVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PureMLPatternSimplifier level variable
    -- ^ Evaluates functions.
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level variable]
    -- ^ Map from symbol IDs to defined functions
    -> PredicateSubstitution level variable
    -- ^ Aggregated children predicate and substitution.
    -> Application level (PureMLPattern level variable)
    -- ^ The pattern to be evaluated
    -> Simplifier (OrOfExpandedPattern level variable, SimplificationProof level)
evaluateApplication
    tools
    simplifier
    symbolIdToEvaluator
    childrenPredicateSubstitution
    app@Application
        { applicationSymbolOrAlias = appHead@SymbolOrAlias
            { symbolOrAliasConstructor = symbolId }
        }
  =
    case Map.lookup symbolId symbolIdToEvaluator of
        Nothing -> if isSortInjection (symAttributes tools appHead)
            then evaluateSortInjection tools unchangedOr app
            else return unchanged
        Just evaluators -> do
            results <- mapM (applyEvaluator app) evaluators
            mergedResults <-
                mapM
                    (mergeWithConditionAndSubstitution
                        tools
                        simplifier
                        childrenPredicateSubstitution
                    )
                    results
            let
                -- Separate into NotApplied and Applied results.
                (notApplied, applied) =
                    partition
                        notApplicable
                        -- TODO(virgil): nub is O(n^2), should do better than
                        -- that.
                        (nub (filter notBottom mergedResults))
                -- All NotApplied results are equivalent, so we just check if
                -- we have at leas one.
                notAppliedTerm = case notApplied of
                    [] -> OrOfExpandedPattern.make []
                    _ -> OrOfExpandedPattern.make [unchangedPatt]
                appliedTerms = map unwrapApplied applied
            return
                ( foldr OrOfExpandedPattern.merge notAppliedTerm appliedTerms
                , SimplificationProof
                )
  where
    notApplicable :: (AttemptedFunction level variable, x) -> Bool
    notApplicable (AttemptedFunction.NotApplicable, _) = True
    notApplicable _ = False

    unwrapApplied
        :: (AttemptedFunction level variable, proof)
        -> OrOfExpandedPattern level variable
    unwrapApplied (AttemptedFunction.Applied term, _proof) = term
    unwrapApplied _ = error "Can only unwrap 'Applied' terms."

    unchangedPatt =
        case childrenPredicateSubstitution of
            PredicateSubstitution {predicate, substitution} ->
                Predicated
                    { term         = asPurePattern $ ApplicationPattern app
                    , predicate    = predicate
                    , substitution = substitution
                    }
    unchangedOr = OrOfExpandedPattern.make [unchangedPatt]
    unchanged = (unchangedOr, SimplificationProof)
    applyEvaluator app' (ApplicationFunctionEvaluator evaluator) =
        evaluator
            tools
            simplifier
            app'
    notBottom =
        \case
            (AttemptedFunction.NotApplicable, _) ->
                True
            (AttemptedFunction.Applied thing, _) ->
                not (OrOfExpandedPattern.isFalse thing)
-- TODO(virgil): Builtins are not expected to recursively simplify until the
-- result stabilizes. Find out if that is indeed the case, then, if needed,
-- move the recursive simplification call from UserDefined.hs here.

evaluateSortInjection
    :: (MetaOrObject level)
    => MetadataTools level StepperAttributes
    -> OrOfExpandedPattern level variable
    -> Application level (PureMLPattern level variable)
    -> Simplifier (OrOfExpandedPattern level variable, SimplificationProof level)
evaluateSortInjection tools unchanged ap = case apChild of
    (App_ apHeadChild grandChildren)
        | isSortInjection (symAttributes tools apHeadChild) ->
        let
            [fromSort', toSort'] = symbolOrAliasParams apHeadChild
            apHeadNew = updateSortInjectionSource apHead fromSort'
        in
            assert (toSort' == fromSort) $
            return
                ( OrOfExpandedPattern.make
                    [ Predicated
                        { term = App_ apHeadNew grandChildren
                        , predicate = makeTruePredicate
                        , substitution = []
                        }
                    ]
                , SimplificationProof
                )
    _ -> return (unchanged, SimplificationProof)
  where
    apHead = applicationSymbolOrAlias ap
    [fromSort, _] = symbolOrAliasParams apHead
    [apChild] = applicationChildren ap
    updateSortInjectionSource
        :: SymbolOrAlias level -> Sort level -> SymbolOrAlias level
    updateSortInjectionSource head1 fromSort1 =
        head1 { symbolOrAliasParams = [fromSort1, toSort1] }
      where
        [_, toSort1] = symbolOrAliasParams head1

{-| 'mergeWithCondition' ands the given condition-substitution to the given
function evaluation.
-}
mergeWithConditionAndSubstitution
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , FreshVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPatternSimplifier level variable
    -- ^ Evaluates functions in a pattern.
    -> PredicateSubstitution level variable
    -- ^ Condition and substitution to add.
    -> (AttemptedFunction level variable, SimplificationProof level)
    -- ^ AttemptedFunction to which the condition should be added.
    -> Simplifier (AttemptedFunction level variable, SimplificationProof level)
mergeWithConditionAndSubstitution
    _ _ _ (AttemptedFunction.NotApplicable, _proof)
  =
    return (AttemptedFunction.NotApplicable, SimplificationProof)
mergeWithConditionAndSubstitution
    tools
    simplifier
    toMerge
    (AttemptedFunction.Applied functionResult, _proof)
  = do
    (evaluated, _proof) <- OrOfExpandedPattern.mergeWithPredicateSubstitution
        tools
        simplifier
        toMerge
        functionResult
    return (AttemptedFunction.Applied evaluated, SimplificationProof)
