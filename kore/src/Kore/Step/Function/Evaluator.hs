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
import           Data.Text.Prettyprint.Doc
                 ( (<+>) )
import qualified Data.Text.Prettyprint.Doc as Pretty

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
                 ( LogMessage, WithLog, logWarning )
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
                 ( extract )
import qualified Kore.Step.Merging.OrPattern as OrPattern
import           Kore.Step.Simplification.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import           Kore.Step.Simplification.Data as Simplifier
import qualified Kore.Step.Simplification.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Unparser
import           Kore.Variables.Fresh

{-| Evaluates functions on an application pattern.
-}
evaluateApplication
    ::  forall variable simplifier
    .   ( Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => Predicate variable
    -- ^ Aggregated children predicate and substitution.
    -> Application Symbol (TermLike variable)
    -- ^ The pattern to be evaluated
    -> simplifier (OrPattern variable)
evaluateApplication childrenPredicate application = do
    substitutionSimplifier <- Simplifier.askSimplifierPredicate
    simplifier <- Simplifier.askSimplifierTermLike
    axiomIdToEvaluator <- Simplifier.askSimplifierAxioms
    let
        afterInj = evaluateSortInjection application
        termLike = synthesize (ApplySymbolF afterInj)

        maybeEvaluatedPattSimplifier =
            maybeEvaluatePattern
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                childrenPredicate
                termLike
                unchanged
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

        unevaluatedSimplifier
          | null axiomIdToEvaluator =
            -- We do not expect to evaluate anything because no evaluators were
            -- provided.
            return unchanged
          | otherwise = do
            warnMissingHook afterInj
            return unchanged

    fromMaybe unevaluatedSimplifier maybeEvaluatedPattSimplifier

{- | If the 'Symbol' has a 'Hook', issue a warning that the hook is missing.

 -}
warnMissingHook
    :: (MonadSimplify simplifier, SortedVariable variable)
    => Application Symbol (TermLike variable) -> simplifier ()
warnMissingHook application
  | Just hook <- symbolHook = do
    let message =
            Pretty.vsep
                [ "Missing hook" <+> Pretty.squotes (Pretty.pretty hook)
                , "while evaluating:"
                , Pretty.indent 4 (unparse application)
                ]
    logWarning (Text.pack $ show message)
  | otherwise =
    return ()
  where
    symbol = applicationSymbolOrAlias application
    symbolHook = (getHook . Attribute.hook) (symbolAttributes symbol)

{-| Evaluates axioms on patterns.
-}
evaluatePattern
    ::  forall variable simplifier
    .   ( Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
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
    -> simplifier (OrPattern variable)
evaluatePattern
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
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
        )

{-| Evaluates axioms on patterns.

Returns Nothing if there is no axiom for the pattern's identifier.
-}
maybeEvaluatePattern
    ::  forall variable simplifier
    .   ( Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
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
    -> Maybe (simplifier (OrPattern variable))
maybeEvaluatePattern
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    childrenPredicate
    patt
    defaultValue
  =
    case maybeEvaluator of
        Nothing -> Nothing
        Just (BuiltinAndAxiomSimplifier evaluator) ->
            Just
            $ traceNonErrorMonad
                D_Function_evaluatePattern
                [ debugArg "axiomIdentifier" identifier ]
            $ do
                result <-
                    evaluator
                        substitutionSimplifier
                        simplifier
                        axiomIdToEvaluator
                        patt
                flattened <- case result of
                    AttemptedAxiom.NotApplicable ->
                        return AttemptedAxiom.NotApplicable
                    AttemptedAxiom.Applied AttemptedAxiomResults
                        { results = orResults
                        , remainders = orRemainders
                        } -> do
                            simplified <- mapM simplifyIfNeeded orResults
                            return
                                (AttemptedAxiom.Applied AttemptedAxiomResults
                                    { results =
                                        MultiOr.flatten simplified
                                    , remainders = orRemainders
                                    }
                                )
                merged <-
                    mergeWithConditionAndSubstitution
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
    identifier = AxiomIdentifier.extract patt

    maybeEvaluator :: Maybe BuiltinAndAxiomSimplifier
    maybeEvaluator = do
        identifier' <- identifier
        Map.lookup identifier' axiomIdToEvaluator

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
    ::  ( SortedVariable variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
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
    ::  ( Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
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
