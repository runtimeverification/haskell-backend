{- |
Module      : Kore.Rewrite.Function.Evaluator
Description : Evaluates functions in a pattern.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Rewrite.Function.Evaluator (
    evaluateApplication,
    evaluatePattern,
) where

import Control.Error (
    ExceptT,
    MaybeT (..),
    exceptT,
    maybeT,
    throwE,
 )
import Control.Monad.Catch (
    MonadThrow,
 )
import qualified Kore.Attribute.Pattern.Simplified as Attribute.Simplified
import Kore.Attribute.Synthetic
import qualified Kore.Internal.MultiOr as MultiOr (
    flatten,
    merge,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Condition,
    Conditional (..),
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.SideCondition.SideCondition as SideCondition (
    Representation,
 )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike as TermLike
import Kore.Log.ErrorBottomTotalFunction (
    errorBottomTotalFunction,
 )
import qualified Kore.Rewrite.Function.Memo as Memo
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify as AttemptedAxiom (
    AttemptedAxiom (..),
 )
import Kore.Simplify.Simplify as Simplifier
import Kore.TopBottom
import Kore.Unparser
import qualified Logic
import Prelude.Kore
import qualified Pretty

-- | Evaluates functions on an application pattern.

-- TODO (thomas.tuegel): Factor out a "function evaluator" object.
-- See also: Kore.Rewrite.Function.Memo.Self
-- Then add a function,
--   memoize :: Evaluator.Self state -> Memo.Self state -> Evaluator.Self state
-- to add memoization to a function evaluator.
evaluateApplication ::
    forall simplifier.
    ( MonadSimplify simplifier
    , MonadThrow simplifier
    ) =>
    -- | The predicate from the configuration
    SideCondition RewritingVariableName ->
    -- | Aggregated children predicate and substitution.
    Condition RewritingVariableName ->
    -- | The pattern to be evaluated
    Application Symbol (TermLike RewritingVariableName) ->
    simplifier (OrPattern RewritingVariableName)
evaluateApplication
    sideCondition
    childrenCondition
    (evaluateSortInjection -> application) =
        finishT $ do
            for_ canMemoize recallOrPattern
            results <-
                maybeEvaluatePattern
                    childrenCondition
                    termLike
                    unevaluated
                    sideCondition
                    & maybeT (unevaluated Nothing) return
                    & lift
            for_ canMemoize (recordOrPattern results)
            let unexpectedBottomResult = Symbol.isFunctional symbol && isBottom results
            when unexpectedBottomResult $
                lift $ errorBottomTotalFunction termLike
            return results
      where
        finishT :: ExceptT r simplifier r -> simplifier r
        finishT = exceptT return return

        Application{applicationSymbolOrAlias = symbol} = application

        termLike = synthesize (ApplySymbolF application)

        unevaluated ::
            Monad m =>
            Maybe SideCondition.Representation ->
            m (OrPattern RewritingVariableName)
        unevaluated maybeSideCondition =
            return $
                OrPattern.fromPattern $
                    Pattern.withCondition
                        (markSimplifiedIfChildren maybeSideCondition termLike)
                        childrenCondition

        markSimplifiedIfChildren ::
            Maybe SideCondition.Representation ->
            TermLike RewritingVariableName ->
            TermLike RewritingVariableName
        markSimplifiedIfChildren Nothing =
            TermLike.setSimplified
                (foldMap TermLike.simplifiedAttribute application)
        markSimplifiedIfChildren (Just condition) =
            TermLike.setSimplified
                ( foldMap TermLike.simplifiedAttribute application
                    <> Attribute.Simplified.simplifiedConditionally condition
                )

        canMemoize
            | Symbol.isMemo symbol
              , ( isTop childrenCondition
                    && isTop (SideCondition.toPredicate sideCondition)
                )
                    || all TermLike.isConstructorLike application =
                traverse asConcrete application
            | otherwise =
                Nothing

        recallOrPattern key = do
            Memo.Self{recall} <- askMemo
            maybeTermLike <- recall key
            let maybeOrPattern =
                    OrPattern.fromTermLike . fromConcrete <$> maybeTermLike
            for_ maybeOrPattern throwE

        recordOrPattern orPattern key
            | [result] <- OrPattern.toPatterns orPattern
              , Just term <- asConcrete (Pattern.term result)
              , -- If the pattern and predicate are concrete, then we expect the predicate
                -- to be fully-evaluated, so it must be Top. It may not be fully-evaluated
                -- due to some uninterpreted function or an unsolved unification problem;
                -- these are not errors, but they are unusual enough that we don't want to
                -- deal with them here.
                isTop (Pattern.predicate result)
              , -- We already checked that childrenCondition has no substitutions, so we
                -- don't expect the result to have any substitutions either. As with the
                -- predicate, it might be possible to have a substitution in some cases,
                -- but they are unusual enough that we don't need to deal with them here.
                isTop (Pattern.substitution result) =
                do
                    Memo.Self{record} <- askMemo
                    record key term
            | otherwise =
                return ()

-- | Evaluates axioms on patterns.
evaluatePattern ::
    forall simplifier.
    MonadSimplify simplifier =>
    -- | The predicate from the configuration
    SideCondition RewritingVariableName ->
    -- | Aggregated children predicate and substitution.
    Condition RewritingVariableName ->
    -- | The pattern to be evaluated
    TermLike RewritingVariableName ->
    -- | The default value
    ( Maybe SideCondition.Representation ->
      simplifier (OrPattern RewritingVariableName)
    ) ->
    simplifier (OrPattern RewritingVariableName)
evaluatePattern
    sideCondition
    childrenCondition
    patt
    defaultValue =
        maybeEvaluatePattern
            childrenCondition
            patt
            defaultValue
            sideCondition
            & maybeT (defaultValue Nothing) return

{- | Evaluates axioms on patterns.

Returns Nothing if there is no axiom for the pattern's identifier.
-}
maybeEvaluatePattern ::
    forall simplifier.
    MonadSimplify simplifier =>
    -- | Aggregated children predicate and substitution.
    Condition RewritingVariableName ->
    -- | The pattern to be evaluated
    TermLike RewritingVariableName ->
    -- | The default value
    ( Maybe SideCondition.Representation ->
      simplifier (OrPattern RewritingVariableName)
    ) ->
    SideCondition RewritingVariableName ->
    MaybeT simplifier (OrPattern RewritingVariableName)
maybeEvaluatePattern
    childrenCondition
    termLike
    defaultValue
    sideCondition =
        do
            BuiltinAndAxiomSimplifier evaluator <- lookupAxiomSimplifier termLike
            lift $ do
                merged <- do
                    result <- evaluator termLike sideCondition
                    flattened <- case result of
                        AttemptedAxiom.Applied
                            AttemptedAxiomResults
                                { results = orResults
                                , remainders = orRemainders
                                } -> do
                                simplified <- OrPattern.traverse simplifyIfNeeded orResults
                                let simplifiedResult = MultiOr.flatten simplified
                                return
                                    ( AttemptedAxiom.Applied
                                        AttemptedAxiomResults
                                            { results = simplifiedResult
                                            , remainders = orRemainders
                                            }
                                    )
                        _ -> return result
                    mergeWithConditionAndSubstitution
                        sideCondition
                        childrenCondition
                        flattened
                case merged of
                    AttemptedAxiom.NotApplicable ->
                        defaultValue Nothing
                    AttemptedAxiom.NotApplicableUntilConditionChanges c ->
                        defaultValue (Just c)
                    AttemptedAxiom.Applied attemptResults ->
                        return $ MultiOr.merge results remainders
                      where
                        AttemptedAxiomResults{results, remainders} =
                            attemptResults
      where
        unchangedPatt =
            Conditional
                { term = termLike
                , predicate = predicate
                , substitution = substitution
                }
          where
            Conditional{term = (), predicate, substitution} = childrenCondition

        simplifyIfNeeded ::
            Pattern RewritingVariableName ->
            simplifier (OrPattern RewritingVariableName)
        simplifyIfNeeded toSimplify
            | toSimplify == unchangedPatt =
                return (OrPattern.fromPattern unchangedPatt)
            | otherwise =
                reevaluateFunctions sideCondition toSimplify

evaluateSortInjection ::
    InternalVariable variable =>
    Application Symbol (TermLike variable) ->
    Application Symbol (TermLike variable)
evaluateSortInjection ap
    | Symbol.isSortInjection apHead =
        case apChild of
            App_ apHeadChild grandChildren
                | Symbol.isSortInjection apHeadChild ->
                    let ~(fromSort', toSort') = sortInjectionSorts apHeadChild
                        apHeadNew = updateSortInjectionSource apHead fromSort'
                        resultApp = apHeadNew grandChildren
                     in assert (toSort' == fromSort) resultApp
            _ -> ap
    | otherwise = ap
  where
    apHead = applicationSymbolOrAlias ap
    ~(fromSort, _) = sortInjectionSorts apHead
    ~apChild = sortInjectionChild ap
    updateSortInjectionSource head1 fromSort1 children =
        Application
            { applicationSymbolOrAlias =
                Symbol.coerceSortInjection head1 fromSort1 toSort1
            , applicationChildren = children
            }
      where
        ~(_, toSort1) = sortInjectionSorts head1

sortInjectionChild :: Unparse a => Application Symbol a -> a
sortInjectionChild application =
    case applicationChildren application of
        [child] -> child
        _ ->
            (error . show . Pretty.vsep)
                [ "Sort injection pattern"
                , Pretty.indent 4 (unparse application)
                , "should have one argument."
                ]

sortInjectionSorts :: Symbol -> (Sort, Sort)
sortInjectionSorts symbol =
    case symbolParams symbol of
        [fromSort, toSort] -> (fromSort, toSort)
        _ ->
            (error . show . Pretty.vsep)
                [ "Sort injection symbol"
                , Pretty.indent 4 (unparse symbol)
                , "should have two sort parameters."
                ]

{- | 'reevaluateFunctions' re-evaluates functions after a user-defined function
was evaluated.
-}
reevaluateFunctions ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    -- | Function evaluation result.
    Pattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
reevaluateFunctions sideCondition rewriting = do
    let (rewritingTerm, rewritingCondition) = Pattern.splitTerm rewriting
    OrPattern.observeAllT $ do
        simplifiedTerm <- simplifyConditionalTerm sideCondition rewritingTerm
        simplifyCondition sideCondition $
            Pattern.andCondition simplifiedTerm rewritingCondition

-- | Ands the given condition-substitution to the given function evaluation.
mergeWithConditionAndSubstitution ::
    MonadSimplify simplifier =>
    -- | Top level condition.
    SideCondition RewritingVariableName ->
    -- | Condition and substitution to add.
    Condition RewritingVariableName ->
    -- | AttemptedAxiom to which the condition should be added.
    AttemptedAxiom RewritingVariableName ->
    simplifier (AttemptedAxiom RewritingVariableName)
mergeWithConditionAndSubstitution _ _ AttemptedAxiom.NotApplicable =
    return AttemptedAxiom.NotApplicable
mergeWithConditionAndSubstitution
    _
    _
    na@(AttemptedAxiom.NotApplicableUntilConditionChanges _) =
        return na
mergeWithConditionAndSubstitution
    sideCondition
    toMerge
    (AttemptedAxiom.Applied AttemptedAxiomResults{results, remainders}) =
        do
            evaluatedResults <- OrPattern.observeAllT $ do
                result <- Logic.scatter results
                simplifyCondition sideCondition $ Pattern.andCondition result toMerge
            evaluatedRemainders <- OrPattern.observeAllT $ do
                remainder <- Logic.scatter remainders
                simplifyCondition sideCondition (Pattern.andCondition remainder toMerge)
            return $
                AttemptedAxiom.Applied
                    AttemptedAxiomResults
                        { results = evaluatedResults
                        , remainders = evaluatedRemainders
                        }
