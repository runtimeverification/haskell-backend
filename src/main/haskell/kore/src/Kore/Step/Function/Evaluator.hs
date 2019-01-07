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
import           Data.Maybe
                 ( isJust )
import           Data.Reflection
                 ( give )
import qualified Data.Text as Text
import           Data.These
                 ( these )

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, PredicateSubstitution, Predicated (..) )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator (..),
                 BuiltinAndAxiomsFunctionEvaluatorMap )
import           Kore.Step.Function.Data as AttemptedFunction
                 ( AttemptedFunction (..) )
import qualified Kore.Step.Merging.OrOfExpandedPattern as OrOfExpandedPattern
                 ( mergeWithPredicateSubstitution )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, isFalse, make, merge, traverseWithPairs )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (..) )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import           Kore.Step.StepperAttributes
                 ( Hook (..), StepperAttributes (..), isSortInjection_ )
import           Kore.Unparser
import           Kore.Variables.Fresh

{-| 'evaluateApplication' - evaluates functions on an application pattern.
-}
evaluateApplication
    ::  forall level variable.
        ( MetaOrObject level
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
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomsFunctionEvaluatorMap level
    -- ^ Map from symbol IDs to defined functions
    -> PredicateSubstitution level variable
    -- ^ Aggregated children predicate and substitution.
    -> CofreeF
        (Application level)
        (Valid (variable level) level)
        (StepPattern level variable)
    -- ^ The pattern to be evaluated
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
evaluateApplication
    tools
    substitutionSimplifier
    simplifier
    symbolIdToEvaluator
    childrenPredicateSubstitution
    validApp@(valid :< app)
  =
    case Map.lookup symbolId symbolIdToEvaluator of
        Nothing
          | give tools isSortInjection_ appHead ->
            evaluateSortInjection tools unchangedOr app
          | Just hook <- getAppHookString
          , not(null symbolIdToEvaluator) ->
            error
                (   "Attempting to evaluate unimplemented hooked operation "
                ++  hook ++ ".\nSymbol: " ++ show (getId symbolId)
                )
          | otherwise ->
            return unchanged
        Just builtinOrAxiomEvaluators ->
            these
                (evaluateWithFunctionAxioms . pure)
                evaluateWithFunctionAxioms
                (\builtinEvaluator axiomEvaluators -> do
                    unprocessedResults <-
                        applyEvaluator validApp builtinEvaluator
                    orResultsWithProofs <-
                        mapM (processResult axiomEvaluators) unprocessedResults
                    let
                        dropProofs :: [(a, SimplificationProof level)] -> [a]
                        dropProofs = map fst
                    return
                        (OrOfExpandedPattern.make
                            (concatMap
                                OrOfExpandedPattern.extractPatterns
                                (dropProofs orResultsWithProofs)
                            )
                        , SimplificationProof
                        )

                )
                builtinOrAxiomEvaluators
  where
    Application { applicationSymbolOrAlias = appHead } = app
    SymbolOrAlias { symbolOrAliasConstructor = symbolId } = appHead

    notApplicable :: (AttemptedFunction level variable, x) -> Bool
    notApplicable (AttemptedFunction.NotApplicable, _) = True
    notApplicable _ = False

    unwrapApplied
        :: (AttemptedFunction level variable, proof)
        -> OrOfExpandedPattern level variable
    unwrapApplied (AttemptedFunction.Applied term, _proof) = term
    unwrapApplied _ = error "Can only unwrap 'Applied' terms."

    appPurePattern = asPurePattern (valid :< ApplicationPattern app)

    processResult
        :: [ApplicationFunctionEvaluator level]
        -> (AttemptedFunction level variable, SimplificationProof level)
        -> Simplifier
            (OrOfExpandedPattern level variable, SimplificationProof level)
    processResult axiomEvaluators (result, proof) =
        case result of
            AttemptedFunction.NotApplicable
              | isAppConcrete
              , Just hook <- getAppHookString ->
                error
                    (   "Expecting hook " ++ hook
                    ++  " to reduce concrete pattern\n\t"
                    ++ show app
                    )
              | otherwise ->
                evaluateWithFunctionAxioms axiomEvaluators
            AttemptedFunction.Applied pat -> return (pat, proof)

    unchangedPatt =
        case childrenPredicateSubstitution of
            Predicated { predicate, substitution } ->
                Predicated
                    { term         = appPurePattern
                    , predicate    = predicate
                    , substitution = substitution
                    }
    unchangedOr = OrOfExpandedPattern.make [unchangedPatt]
    unchanged = (unchangedOr, SimplificationProof)

    applyEvaluator app' (ApplicationFunctionEvaluator evaluator) = do
        results <- evaluator
            tools
            substitutionSimplifier
            simplifier
            app'
        mapM
            (mergeWithConditionAndSubstitution
                tools
                substitutionSimplifier
                simplifier
                childrenPredicateSubstitution
            )
            results

    notBottom =
        \case
            (AttemptedFunction.NotApplicable, _) ->
                True
            (AttemptedFunction.Applied thing, _) ->
                not (OrOfExpandedPattern.isFalse thing)

    isAppConcrete = isJust (asConcretePurePattern appPurePattern)
    getAppHookString =
        Text.unpack <$> (getHook . hook . symAttributes tools) appHead

    evaluateWithFunctionAxioms evaluators = do
        resultsLists <- mapM (applyEvaluator validApp) evaluators
        let
            results
                ::  [   ( AttemptedFunction level variable
                        , SimplificationProof level
                        )
                    ]
            results = concat resultsLists
            -- Separate into NotApplied and Applied results.
            (notApplied, applied) =
                partition
                    notApplicable
                    -- TODO(virgil): nub is O(n^2), should do better than
                    -- that.
                    (nub (filter notBottom results))
            -- All NotApplied results are equivalent, so we just check if
            -- we have at least one.
            notAppliedTerm = case notApplied of
                [] -> OrOfExpandedPattern.make []
                _ -> OrOfExpandedPattern.make [unchangedPatt]
                -- TODO(virgil): attach a predicate identifying the
                -- rule which didn't apply; returning the pattern unchanged
                -- is not really correct as we doesn't explain how we got
                -- here.
            appliedTerms = map unwrapApplied applied
            unsimplifiedResults :: OrOfExpandedPattern level variable
            unsimplifiedResults =
                foldr OrOfExpandedPattern.merge notAppliedTerm appliedTerms
            simplifiedResults :: Simplifier (OrOfExpandedPattern level variable)
            simplifiedResults = do
                simplifiedLists <- mapM
                    simplifyIfNeeded
                    (OrOfExpandedPattern.extractPatterns unsimplifiedResults)
                return (OrOfExpandedPattern.make (concat simplifiedLists))
            simplifyIfNeeded
                :: ExpandedPattern level variable
                -> Simplifier [ExpandedPattern level variable]
            simplifyIfNeeded result =
                if result == unchangedPatt
                    then return [unchangedPatt]
                    else do
                        orPatt <- reevaluateFunctions
                            tools
                            substitutionSimplifier
                            simplifier
                            result
                        return (OrOfExpandedPattern.extractPatterns orPatt)
        simplified <- simplifiedResults
        return
            ( simplified
            , SimplificationProof
            )

{-| 'reevaluateFunctions' re-evaluates functions after a user-defined function
was evaluated.
-}
reevaluateFunctions
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions in patterns.
    -> ExpandedPattern level variable
    -- ^ Function evaluation result.
    -> Simplifier (OrOfExpandedPattern level variable)
reevaluateFunctions
    tools
    substitutionSimplifier
    wrappedSimplifier@(StepPatternSimplifier simplifier)
    Predicated
        { term   = rewrittenPattern
        , predicate = rewritingCondition
        , substitution = rewrittenSubstitution
        }
  = do
    (pattOr , _proof) <-
        simplifier substitutionSimplifier rewrittenPattern
    (mergedPatt, _proof) <-
        OrOfExpandedPattern.mergeWithPredicateSubstitution
            tools
            substitutionSimplifier
            wrappedSimplifier
            Predicated
                { term = ()
                , predicate = rewritingCondition
                , substitution = rewrittenSubstitution
                }
            pattOr
    (evaluatedPatt, _) <-
        OrOfExpandedPattern.traverseWithPairs
            (ExpandedPattern.simplifyPredicate
                tools substitutionSimplifier wrappedSimplifier
            )
            mergedPatt
    return evaluatedPatt

evaluateSortInjection
    :: (MetaOrObject level, Ord (variable level))
    => MetadataTools level StepperAttributes
    -> OrOfExpandedPattern level variable
    -> Application level (StepPattern level variable)
    -> Simplifier (OrOfExpandedPattern level variable, SimplificationProof level)
evaluateSortInjection tools unchanged ap = case apChild of
    (App_ apHeadChild grandChildren)
      | give tools isSortInjection_ apHeadChild ->
        let
            [fromSort', toSort'] = symbolOrAliasParams apHeadChild
            apHeadNew = updateSortInjectionSource apHead fromSort'
        in
            assert (toSort' == fromSort) $
            return
                ( OrOfExpandedPattern.make
                    [ Predicated
                        { term = apHeadNew grandChildren
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                , SimplificationProof
                )
    _ -> return (unchanged, SimplificationProof)
  where
    apHead = applicationSymbolOrAlias ap
    [fromSort, _] = symbolOrAliasParams apHead
    [apChild] = applicationChildren ap
    updateSortInjectionSource head1 fromSort1 =
        mkApp toSort1 head1 { symbolOrAliasParams = [fromSort1, toSort1] }
      where
        [_, toSort1] = symbolOrAliasParams head1

{-| 'mergeWithCondition' ands the given condition-substitution to the given
function evaluation.
-}
mergeWithConditionAndSubstitution
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
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions in a pattern.
    -> PredicateSubstitution level variable
    -- ^ Condition and substitution to add.
    -> (AttemptedFunction level variable, SimplificationProof level)
    -- ^ AttemptedFunction to which the condition should be added.
    -> Simplifier (AttemptedFunction level variable, SimplificationProof level)
mergeWithConditionAndSubstitution
    _ _ _ _ (AttemptedFunction.NotApplicable, _proof)
  =
    return (AttemptedFunction.NotApplicable, SimplificationProof)
mergeWithConditionAndSubstitution
    tools
    substitutionSimplifier
    simplifier
    toMerge
    (AttemptedFunction.Applied functionResult, _proof)
  = do
    (evaluated, _proof) <- OrOfExpandedPattern.mergeWithPredicateSubstitution
        tools
        substitutionSimplifier
        simplifier
        toMerge
        functionResult
    return (AttemptedFunction.Applied evaluated, SimplificationProof)
