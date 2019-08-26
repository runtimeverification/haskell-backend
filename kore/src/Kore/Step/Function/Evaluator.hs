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
    , evaluateOnce
    ) where

import           Control.Applicative
                 ( Alternative (empty) )
import           Control.Error
                 ( MaybeT )
import qualified Control.Error as Error
import           Control.Exception
                 ( assert )
import qualified Control.Monad.Trans as Monad.Trans
import           Data.Text
                 ( Text )
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
import qualified Kore.Step.Substitution as Substitution
import qualified Kore.Unification.Unify as Unification
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
    -- ^ The predicate from the configuration
    -> Predicate variable
    -- ^ Aggregated children predicate and substitution.
    -> Application Symbol (TermLike variable)
    -- ^ The pattern to be evaluated
    -> simplifier (OrPattern variable)
evaluateApplication configurationPredicate childrenPredicate application = do
    hasSimplifierAxioms <- not . null <$> Simplifier.askSimplifierAxioms
    let
        afterInj = evaluateSortInjection application
        termLike = synthesize (ApplySymbolF afterInj)
        unchanged =
            OrPattern.fromPattern
            $ Pattern.withCondition termLike childrenPredicate

        symbol = applicationSymbolOrAlias afterInj
        symbolHook = (getHook . Attribute.hook) (symbolAttributes symbol)
        -- Return the input when there are no evaluators for the symbol.
        unevaluatedSimplifier
          | hasSimplifierAxioms
          , Just hook <- symbolHook
          = do
            warnMissingHook hook afterInj
            -- Mark the result so we do not attempt to evaluate it again. This
            -- prevents spamming the warning above, but re-evaluation will never
            -- succeed anyway if there are no evaluators for this symbol!
            return $ (fmap . fmap) mkEvaluated unchanged
          | otherwise =
            return unchanged

    Error.maybeT unevaluatedSimplifier return
        $ maybeEvaluatePattern childrenPredicate termLike unchanged configurationPredicate

{- | If the 'Symbol' has a 'Hook', issue a warning that the hook is missing.

 -}
warnMissingHook
    :: (MonadSimplify simplifier, SortedVariable variable)
    => Text -> Application Symbol (TermLike variable) -> simplifier ()
warnMissingHook hook application = do
    let message =
            Pretty.vsep
                [ "Missing hook" <+> Pretty.squotes (Pretty.pretty hook)
                , "while evaluating:"
                , Pretty.indent 4 (unparse application)
                ]
    logWarning (Text.pack $ show message)

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
    => Predicate variable
    -- ^ The predicate from the configuration
    -> Predicate variable
    -- ^ Aggregated children predicate and substitution.
    -> TermLike variable
    -- ^ The pattern to be evaluated
    -> OrPattern variable
    -- ^ The default value
    -> simplifier (OrPattern variable)
evaluatePattern configurationPredicate childrenPredicate patt defaultValue =
    Error.maybeT (return defaultValue) return
    $ maybeEvaluatePattern childrenPredicate patt defaultValue configurationPredicate

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
    => Predicate variable
    -- ^ Aggregated children predicate and substitution.
    -> TermLike variable
    -- ^ The pattern to be evaluated
    -> OrPattern variable
    -- ^ The default value
    -> Predicate variable
    -- ^ The predicate from the configuration
    -> MaybeT simplifier (OrPattern variable)
maybeEvaluatePattern childrenPredicate termLike defaultValue configurationPredicate =
    Simplifier.lookupSimplifierAxiom termLike
    >>= \(BuiltinAndAxiomSimplifier evaluator) -> tracing $ do
        axiomIdToEvaluator <- Simplifier.askSimplifierAxioms
        substitutionSimplifier <- Simplifier.askSimplifierPredicate
        simplifier <- Simplifier.askSimplifierTermLike
        result <- axiomEvaluationTracing $
            evaluator
                substitutionSimplifier
                simplifier
                axiomIdToEvaluator
                termLike
                configurationPredicate
        flattened <- case result of
            AttemptedAxiom.NotApplicable ->
                return AttemptedAxiom.NotApplicable
            AttemptedAxiom.Applied AttemptedAxiomResults
                { results = orResults
                , remainders = orRemainders
                } -> do
                    simplified <- resimplificationTracing (length orResults) $
                        mapM simplifyIfNeeded orResults
                    return
                        (AttemptedAxiom.Applied AttemptedAxiomResults
                            { results =
                                MultiOr.flatten simplified
                            , remainders = orRemainders
                            }
                        )
        merged <- mergeTracing $
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
    identifier = AxiomIdentifier.matchAxiomIdentifier termLike

    tracing =
        traceMaybeT
            D_Function_evaluatePattern
            [ debugArg "axiomIdentifier" identifier ]
        . case identifier of
            Nothing -> id
            Just identifier' ->
                Profile.equalitySimplification identifier' termLike

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
            { term         = termLike
            , predicate    = predicate
            , substitution = substitution
            }
      where
        Conditional { term = (), predicate, substitution } = childrenPredicate

    simplifyIfNeeded
        :: Pattern variable -> MaybeT simplifier (OrPattern variable)
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

{- | Attempt once to evaluate the 'TermLike' with user-defined axioms.

The result is 'Nothing' if there are no applicable user-defined axioms. The
result is not simplified or re-evaluated.

 -}
evaluateOnce
    ::  forall variable simplifier
    .   ( Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        , MonadSimplify simplifier
        , WithLog LogMessage simplifier
        )
    => Predicate variable
    -- ^ The predicate from the configuration
    -> Predicate variable
    -- ^ Aggregated children predicate and substitution.
    -> TermLike variable
    -- ^ The pattern to be evaluated
    -> MaybeT (BranchT simplifier) (Pattern variable)
evaluateOnce configurationPredicate predicate termLike = do
    simplifierAxiom <- Simplifier.lookupSimplifierAxiom termLike
    result <- Simplifier.runBuiltinAndAxiomSimplifier
        simplifierAxiom
        configurationPredicate
        termLike
    case result of
        AttemptedAxiom.NotApplicable -> empty
        AttemptedAxiom.Applied attemptedAxiomResults ->
            (>>= Monad.Trans.lift . scatter) . Unification.maybeUnifierT $ do
                pattern' <- Unification.scatter $ results <> remainders
                let (termLike', predicate') = Pattern.splitTerm pattern'
                    predicate'' = predicate <> predicate'
                normalized <- Substitution.normalizeExcept predicate''
                return $ Pattern.withCondition termLike' normalized
          where
            AttemptedAxiomResults { results, remainders } =
                attemptedAxiomResults
