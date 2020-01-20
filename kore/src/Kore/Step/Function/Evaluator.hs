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

import Control.Error
    ( ExceptT
    , MaybeT (..)
    , exceptT
    , maybeT
    , throwE
    )
import Control.Exception
    ( assert
    )
import qualified Control.Monad.Trans as Trans
import qualified Data.Foldable as Foldable
import Data.Function
import Data.Text
    ( Text
    )
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Branch as BranchT
import Kore.Attribute.Synthetic
import qualified Kore.Internal.MultiOr as MultiOr
    ( flatten
    , merge
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Condition
    , Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( andCondition
    )
import qualified Kore.Internal.Symbol as Symbol
import Kore.Internal.TermLike as TermLike
import qualified Kore.Log.DebugAxiomEvaluation as DebugAxiomEvaluation
    ( end
    , klabelIdentifier
    , notEvaluated
    , reevaluation
    , start
    )
import qualified Kore.Profiler.Profile as Profile
    ( axiomBranching
    , axiomEvaluation
    , equalitySimplification
    , mergeSubstitutions
    , resimplification
    )
import Kore.Step.Axiom.Identifier
    ( AxiomIdentifier
    )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
import qualified Kore.Step.Function.Memo as Memo
import Kore.Step.Simplification.Simplify as AttemptedAxiom
    ( AttemptedAxiom (..)
    )
import Kore.Step.Simplification.Simplify as Simplifier
import qualified Kore.Step.Simplification.Simplify as AttemptedAxiomResults
    ( AttemptedAxiomResults (..)
    )
import Kore.TopBottom
import Kore.Unparser

{-| Evaluates functions on an application pattern.
-}
-- TODO (thomas.tuegel): Factor out a "function evaluator" object.
-- See also: Kore.Step.Function.Memo.Self
-- Then add a function,
--   memoize :: Evaluator.Self state -> Memo.Self state -> Evaluator.Self state
-- to add memoization to a function evaluator.
evaluateApplication
    :: forall variable simplifier
    .  ( SimplifierVariable variable
       , MonadSimplify simplifier
       )
    => SideCondition variable
    -- ^ The predicate from the configuration
    -> Condition variable
    -- ^ Aggregated children predicate and substitution.
    -> Application Symbol (TermLike variable)
    -- ^ The pattern to be evaluated
    -> simplifier (OrPattern variable)
evaluateApplication
    sideCondition
    childrenCondition
    (evaluateSortInjection -> application)
  = finishT $ do
    Foldable.for_ canMemoize recallOrPattern
    results <-
        maybeEvaluatePattern
            childrenCondition
            termLike
            unevaluated
            sideCondition
        & maybeT (return unevaluated) return
        & Trans.lift
    Foldable.for_ canMemoize (recordOrPattern results)
    return results
  where
    finishT :: ExceptT r simplifier r -> simplifier r
    finishT = exceptT return return

    Application { applicationSymbolOrAlias = symbol } = application

    termLike = synthesize (ApplySymbolF application)
    unevaluated =
        OrPattern.fromPattern
        $ Pattern.withCondition
            (markSimplifiedIfChildren termLike)
            childrenCondition

    markSimplifiedIfChildren = TermLike.setSimplified
        (Foldable.foldMap TermLike.simplifiedAttribute application)

    canMemoize
      | Symbol.isMemo symbol
      , (isTop childrenCondition && isTop sideCondition)
        || all TermLike.isConstructorLike application
      = traverse asConcrete application
      | otherwise
      = Nothing

    recallOrPattern key = do
        Memo.Self { recall } <- askMemo
        maybeTermLike <- recall key
        let maybeOrPattern =
                OrPattern.fromTermLike . fromConcrete <$> maybeTermLike
        Foldable.for_ maybeOrPattern throwE

    recordOrPattern orPattern key
      | [result] <- OrPattern.toPatterns orPattern
      , Just term <- asConcrete (Pattern.term result)
      -- If the pattern and predicate are concrete, then we expect the predicate
      -- to be fully-evaluated, so it must be Top. It may not be fully-evaluated
      -- due to some uninterpreted function or an unsolved unification problem;
      -- these are not errors, but they are unusual enough that we don't want to
      -- deal with them here.
      , isTop (Pattern.predicate result)
      -- We already checked that childrenCondition has no substitutions, so we
      -- don't expect the result to have any substitutions either. As with the
      -- predicate, it might be possible to have a substitution in some cases,
      -- but they are unusual enough that we don't need to deal with them here.
      , isTop (Pattern.substitution result)
      = do
        Memo.Self { record } <- askMemo
        record key term
      | otherwise
      = return ()

{-| Evaluates axioms on patterns.
-}
evaluatePattern
    :: forall variable simplifier
    .  SimplifierVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -- ^ The predicate from the configuration
    -> Condition variable
    -- ^ Aggregated children predicate and substitution.
    -> TermLike variable
    -- ^ The pattern to be evaluated
    -> OrPattern variable
    -- ^ The default value
    -> simplifier (OrPattern variable)
evaluatePattern
    sideCondition
    childrenCondition
    patt
    defaultValue
  =
    maybeEvaluatePattern
        childrenCondition
        patt
        defaultValue
        sideCondition
    & maybeT (return defaultValue) return

{-| Evaluates axioms on patterns.

Returns Nothing if there is no axiom for the pattern's identifier.
-}
maybeEvaluatePattern
    :: forall variable simplifier
    .  SimplifierVariable variable
    => MonadSimplify simplifier
    => Condition variable
    -- ^ Aggregated children predicate and substitution.
    -> TermLike variable
    -- ^ The pattern to be evaluated
    -> OrPattern variable
    -- ^ The default value
    -> SideCondition variable
    -> MaybeT simplifier (OrPattern variable)
maybeEvaluatePattern
    childrenCondition
    termLike
    defaultValue
    sideCondition
  = do
    BuiltinAndAxiomSimplifier evaluator <- lookupAxiomSimplifier termLike
    Trans.lift . tracing $ do
        merged <- bracketAxiomEvaluationLog $ do
            let sideConditions =
                    sideCondition
                    `SideCondition.andCondition` childrenCondition
            result <-
                Profile.axiomEvaluation identifier
                $ evaluator termLike sideConditions
            flattened <- case result of
                AttemptedAxiom.NotApplicable -> do
                    DebugAxiomEvaluation.notEvaluated
                        identifier
                        klabelIdentifier
                    return AttemptedAxiom.NotApplicable
                AttemptedAxiom.Applied AttemptedAxiomResults
                    { results = orResults
                    , remainders = orRemainders
                    } -> do
                        DebugAxiomEvaluation.reevaluation
                            identifier
                            klabelIdentifier
                        simplified <-
                            Profile.resimplification
                                identifier (length orResults)
                            $ mapM simplifyIfNeeded orResults
                        let simplifiedResult = MultiOr.flatten simplified
                        Profile.axiomBranching
                            identifier
                            (length orResults)
                            (length simplifiedResult)
                        return
                            (AttemptedAxiom.Applied AttemptedAxiomResults
                                { results = simplifiedResult
                                , remainders = orRemainders
                                }
                            )
            Profile.mergeSubstitutions identifier
                $ mergeWithConditionAndSubstitution
                    sideCondition
                    childrenCondition
                    flattened
        case merged of
            AttemptedAxiom.NotApplicable ->
                return defaultValue
            AttemptedAxiom.Applied attemptResults ->
                return $ MultiOr.merge results remainders
                where
                AttemptedAxiomResults { results, remainders } =
                    attemptResults
  where
    identifier :: Maybe AxiomIdentifier
    identifier = AxiomIdentifier.matchAxiomIdentifier termLike

    klabelIdentifier :: Maybe Text
    klabelIdentifier = DebugAxiomEvaluation.klabelIdentifier termLike

    tracing = Profile.equalitySimplification identifier termLike

    bracketAxiomEvaluationLog
        :: simplifier (AttemptedAxiom variable)
        -> simplifier (AttemptedAxiom variable)
    bracketAxiomEvaluationLog action = do
        DebugAxiomEvaluation.start identifier klabelIdentifier
        result <- action
        DebugAxiomEvaluation.end identifier klabelIdentifier
        return result

    unchangedPatt =
        Conditional
            { term         = termLike
            , predicate    = predicate
            , substitution = substitution
            }
      where
        Conditional { term = (), predicate, substitution } = childrenCondition

    simplifyIfNeeded :: Pattern variable -> simplifier (OrPattern variable)
    simplifyIfNeeded toSimplify
      | toSimplify == unchangedPatt =
        return (OrPattern.fromPattern unchangedPatt)
      | otherwise =
        reevaluateFunctions sideCondition toSimplify

evaluateSortInjection
    :: InternalVariable variable
    => Application Symbol (TermLike variable)
    -> Application Symbol (TermLike variable)
evaluateSortInjection ap
  | Symbol.isSortInjection apHead
  = case apChild of
    App_ apHeadChild grandChildren
      | Symbol.isSortInjection apHeadChild ->
        let
            (fromSort', toSort') = sortInjectionSorts apHeadChild
            apHeadNew = updateSortInjectionSource apHead fromSort'
            resultApp = apHeadNew grandChildren
        in
            assert (toSort' == fromSort) resultApp
    _ -> ap
  | otherwise = ap
  where
    apHead = applicationSymbolOrAlias ap
    (fromSort, _) = sortInjectionSorts apHead
    apChild = sortInjectionChild ap
    updateSortInjectionSource head1 fromSort1 children =
        Application
            { applicationSymbolOrAlias =
                Symbol.coerceSortInjection head1 fromSort1 toSort1
            , applicationChildren = children
            }
      where
        (_, toSort1) = sortInjectionSorts head1

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

{-| 'reevaluateFunctions' re-evaluates functions after a user-defined function
was evaluated.
-}
reevaluateFunctions
    :: SimplifierVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -> Pattern variable
    -- ^ Function evaluation result.
    -> simplifier (OrPattern variable)
reevaluateFunctions sideCondition rewriting = do
    let (rewritingTerm, rewritingCondition) = Pattern.splitTerm rewriting
    orResults <- BranchT.gather $ do
        simplifiedTerm <- simplifyConditionalTerm sideCondition rewritingTerm
        simplifyCondition sideCondition
            $ Pattern.andCondition simplifiedTerm rewritingCondition
    return (OrPattern.fromPatterns orResults)

{-| Ands the given condition-substitution to the given function evaluation.
-}
mergeWithConditionAndSubstitution
    :: SimplifierVariable variable
    => MonadSimplify simplifier
    => SideCondition variable
    -- ^ Top level condition.
    -> Condition variable
    -- ^ Condition and substitution to add.
    -> AttemptedAxiom variable
    -- ^ AttemptedAxiom to which the condition should be added.
    -> simplifier (AttemptedAxiom variable)
mergeWithConditionAndSubstitution _ _ AttemptedAxiom.NotApplicable =
    return AttemptedAxiom.NotApplicable
mergeWithConditionAndSubstitution
    sideCondition
    toMerge
    (AttemptedAxiom.Applied AttemptedAxiomResults { results, remainders })
  = do
    evaluatedResults <- fmap OrPattern.fromPatterns . BranchT.gather $ do
        result <- BranchT.scatter results
        simplifyCondition sideCondition $ Pattern.andCondition result toMerge
    evaluatedRemainders <- fmap OrPattern.fromPatterns . BranchT.gather $ do
        remainder <- BranchT.scatter remainders
        simplifyCondition sideCondition (Pattern.andCondition remainder toMerge)
    return $ AttemptedAxiom.Applied AttemptedAxiomResults
        { results = evaluatedResults
        , remainders = evaluatedRemainders
        }
