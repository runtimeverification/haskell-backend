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
    , evaluatePattern
    ) where

import           Control.Exception
                 ( assert )
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )
import qualified Data.Text as Text

import           Kore.Attribute.Hook
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.Attribute.Synthetic
import           Kore.Debug
import qualified Kore.Internal.MultiOr as MultiOr
                 ( flatten, merge, mergeAll )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Conditional (..), Pattern, Predicate )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Symbol as Symbol
import           Kore.Internal.TermLike
import           Kore.Logger
                 ( LogMessage, WithLog )
import qualified Kore.Profiler.Profile as Profile
                 ( axiomEvaluation, equalitySimplification, mergeSubstitutions,
                 resimplification )
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import qualified Kore.Step.Merging.OrPattern as OrPattern
import           Kore.Step.Simplification.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import           Kore.Step.Simplification.Data as Simplifier
import qualified Kore.Step.Simplification.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )
import qualified Kore.Step.Simplification.Pattern as Pattern

{-| Evaluates functions on an application pattern.
-}
evaluateApplication
    ::  forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => Predicate variable
    -- ^ The predicate from the configuration
    -> Predicate variable
    -- ^ Aggregated children predicate and substitution.
    -> Application Symbol (TermLike variable)
    -- ^ The pattern to be evaluated
    -> simplifier (OrPattern variable)
evaluateApplication configurationPredicate childrenPredicate application =
    cachedOr $ do
    substitutionSimplifier <- Simplifier.askSimplifierPredicate
    simplifier <- Simplifier.askSimplifierTermLike
    axiomIdToEvaluator <- Simplifier.askSimplifierAxioms
    let
        afterInj = evaluateSortInjection application
        Application { applicationSymbolOrAlias = appHead } = afterInj
        Symbol { symbolConstructor = symbolId } = appHead
        termLike = synthesize (ApplySymbolF afterInj)

        maybeEvaluatedPattSimplifier =
            maybeEvaluatePattern
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                childrenPredicate
                termLike
                unchanged
                configurationPredicate
        unchangedPatt =
            Conditional
                { term         = termLike
                , predicate    = predicate
                , substitution = substitution
                }
          where
            Conditional { term = (), predicate, substitution } =
                childrenPredicate
        unchanged = OrPattern.fromPattern unchangedPatt

        getSymbolHook = getHook . Attribute.hook . symbolAttributes
        getAppHookString = Text.unpack <$> getSymbolHook appHead

    case maybeEvaluatedPattSimplifier of
        Nothing
          | Just hook <- getAppHookString
          , not(null axiomIdToEvaluator) ->
            error
                (   "Attempting to evaluate unimplemented hooked operation "
                ++  hook ++ ".\nSymbol: " ++ getIdForError symbolId
                )
          | otherwise ->
            return unchanged
        Just evaluatedPattSimplifier -> evaluatedPattSimplifier

  where
    cachedOr compute = do
        let key = (configurationPredicate, childrenPredicate, application)
        simplifierRecall key >>= \case
            Just value -> return value
            Nothing -> do
                value <- compute
                simplifierMemo key value
                return value

{-| Evaluates axioms on patterns.
-}
evaluatePattern
    ::  forall variable simplifier
    .   ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Predicate variable
    -- ^ The predicate from the configuration
    -> Predicate variable
    -- ^ Aggregated children predicate and substitution.
    -> TermLike variable
    -- ^ The pattern to be evaluated
    -> OrPattern variable
    -- ^ The default value
    -> simplifier (OrPattern variable)
evaluatePattern
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    configurationPredicate
    childrenPredicate
    patt
    defaultValue
  =
    fromMaybe
        (return defaultValue)
        (maybeEvaluatePattern
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            childrenPredicate
            patt
            defaultValue
            configurationPredicate
        )

{-| Evaluates axioms on patterns.

Returns Nothing if there is no axiom for the pattern's identifier.
-}
maybeEvaluatePattern
    ::  forall variable simplifier
    .   ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Predicate variable
    -- ^ Aggregated children predicate and substitution.
    -> TermLike variable
    -- ^ The pattern to be evaluated
    -> OrPattern variable
    -- ^ The default value
    -> Predicate variable
    -> Maybe (simplifier (OrPattern variable))
maybeEvaluatePattern
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    childrenPredicate
    patt
    defaultValue
    configurationPredicate
  =
    case maybeEvaluator of
        Nothing -> Nothing
        Just (BuiltinAndAxiomSimplifier evaluator) ->
            Just . tracing $ do
                result <- axiomEvaluationTracing $
                    evaluator
                        substitutionSimplifier
                        simplifier
                        axiomIdToEvaluator
                        patt
                        configurationPredicate
                flattened <- case result of
                    AttemptedAxiom.NotApplicable ->
                        return AttemptedAxiom.NotApplicable
                    AttemptedAxiom.Applied AttemptedAxiomResults
                        { results = orResults
                        , remainders = orRemainders
                        } -> do
                            simplified <-
                                resimplificationTracing (length orResults)
                                $ mapM simplifyIfNeeded orResults
                            return
                                (AttemptedAxiom.Applied AttemptedAxiomResults
                                    { results =
                                        MultiOr.flatten simplified
                                    , remainders = orRemainders
                                    }
                                )
                merged <-
                    mergeTracing
                    $ mergeWithConditionAndSubstitution
                        childrenPredicate
                        flattened
                case merged of
                    AttemptedAxiom.NotApplicable -> return defaultValue
                    AttemptedAxiom.Applied attemptResults ->
                        return $ MultiOr.merge results remainders
                      where
                        AttemptedAxiomResults { results, remainders } =
                            attemptResults
  where
    identifier :: Maybe AxiomIdentifier
    identifier = AxiomIdentifier.matchAxiomIdentifier patt

    maybeEvaluator :: Maybe BuiltinAndAxiomSimplifier
    maybeEvaluator = do
        identifier' <- identifier
        Map.lookup identifier' axiomIdToEvaluator

    tracing =
        traceNonErrorMonad
            D_Function_evaluatePattern
            [ debugArg "axiomIdentifier" identifier ]
        . case identifier of
            Nothing -> id
            Just identifier' ->
                Profile.equalitySimplification identifier' patt

    axiomEvaluationTracing = maybe id Profile.axiomEvaluation identifier
    resimplificationTracing resultCount =
        case identifier of
            Nothing -> id
            Just identifier' -> Profile.resimplification identifier' resultCount
    mergeTracing =
        case identifier of
            Nothing -> id
            Just identifier' -> Profile.mergeSubstitutions identifier'

    unchangedPatt =
        Conditional
            { term         = patt
            , predicate    = predicate
            , substitution = substitution
            }
      where
        Conditional { term = (), predicate, substitution } = childrenPredicate

    simplifyIfNeeded :: Pattern variable -> simplifier (OrPattern variable)
    simplifyIfNeeded toSimplify
      | toSimplify == unchangedPatt =
        return (OrPattern.fromPattern unchangedPatt)
      | otherwise =
        reevaluateFunctions toSimplify

evaluateSortInjection
    :: Ord variable
    => Application Symbol (TermLike variable)
    -> Application Symbol (TermLike variable)
evaluateSortInjection ap
  | Symbol.isSortInjection apHead
  = case apChild of
    App_ apHeadChild grandChildren
      | Symbol.isSortInjection apHeadChild ->
        let
            [fromSort', toSort'] = symbolParams apHeadChild
            apHeadNew = updateSortInjectionSource apHead fromSort'
            resultApp = apHeadNew grandChildren
        in
            assert (toSort' == fromSort) resultApp
    _ -> ap
  | otherwise = ap
  where
    apHead = applicationSymbolOrAlias ap
    [fromSort, _] = symbolParams apHead
    [apChild] = applicationChildren ap
    updateSortInjectionSource head1 fromSort1 children =
        Application
            { applicationSymbolOrAlias =
                Symbol.coerceSortInjection head1 fromSort1 toSort1
            , applicationChildren = children
            }
      where
        [_, toSort1] = symbolParams head1

{-| 'reevaluateFunctions' re-evaluates functions after a user-defined function
was evaluated.
-}
reevaluateFunctions
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Pattern variable
    -- ^ Function evaluation result.
    -> simplifier (OrPattern variable)
reevaluateFunctions rewriting = do
    pattOr <- simplifyTerm (Pattern.term rewriting)
    mergedPatt <-
        OrPattern.mergeWithPredicate (Pattern.withoutTerm rewriting) pattOr
    orResults <- BranchT.gather $ traverse Pattern.simplifyPredicate mergedPatt
    return (MultiOr.mergeAll orResults)

{-| Ands the given condition-substitution to the given function evaluation.
-}
mergeWithConditionAndSubstitution
    ::  ( SimplifierVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Predicate variable
    -- ^ Condition and substitution to add.
    -> AttemptedAxiom variable
    -- ^ AttemptedAxiom to which the condition should be added.
    -> simplifier (AttemptedAxiom variable)
mergeWithConditionAndSubstitution _ AttemptedAxiom.NotApplicable =
    return AttemptedAxiom.NotApplicable
mergeWithConditionAndSubstitution
    toMerge
    (AttemptedAxiom.Applied AttemptedAxiomResults { results, remainders })
  = do
    evaluatedResults <- OrPattern.mergeWithPredicate toMerge results
    evaluatedRemainders <- OrPattern.mergeWithPredicate toMerge remainders
    return $ AttemptedAxiom.Applied AttemptedAxiomResults
        { results = evaluatedResults
        , remainders = evaluatedRemainders
        }
