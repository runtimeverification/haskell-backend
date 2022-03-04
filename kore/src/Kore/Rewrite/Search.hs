{- |
Module      : Kore.Rewrite.Search
Description : Search functionality matching krun API
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
Maintainer  : traian.serbanuta@runtimeverification.com
-}
module Kore.Rewrite.Search (
    Config (..),
    SearchType (..),
    searchGraph,
    matchWith,
) where

import Control.Error (
    MaybeT (..),
 )
import Data.Limit (
    Limit (..),
 )
import Data.Limit qualified as Limit
import Data.Map.Strict qualified as Map
import Kore.Internal.Condition qualified as Condition (
    bottom,
    fromSubstitution,
 )
import Kore.Internal.MultiOr qualified as MultiOr (
    make,
 )
import Kore.Internal.OrCondition (
    OrCondition,
 )
import Kore.Internal.Pattern (
    Condition,
    Pattern,
 )
import Kore.Internal.Pattern qualified as Conditional
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.Substitution (
    Substitution,
 )
import Kore.Rewrite.Axiom.Matcher (
    MatchResult,
    matchIncremental,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Rewrite.SMT.Evaluator qualified as SMT (
    evalConditional,
 )
import Kore.Rewrite.Strategy qualified as Strategy
import Kore.Rewrite.Substitution (
    mergePredicatesAndSubstitutions,
 )
import Kore.Simplify.Simplify
import Kore.TopBottom
import Logic (
    LogicT,
 )
import Logic qualified
import Numeric.Natural (
    Natural,
 )
import Prelude.Kore

{- | Which configurations are considered for matching?

See also: 'searchGraph'
-}
data SearchType
    = -- | Reachable in exactly one execution step
      ONE
    | -- | Reachable configurations which cannot be rewritten anymore
      FINAL
    | -- | All reachable configurations
      STAR
    | -- | All configurations reachable in at least one step
      PLUS
    deriving stock (Eq, Show)

-- | Search options
data Config = Config
    { -- | maximum number of solutions
      bound :: !(Limit Natural)
    , searchType :: !SearchType
    }

{- | Construct a list of solutions to the execution search problem.

The execution tree can be generated with 'Kore.Rewrite.Strategy.runStrategy' or any
of the related functions in "Kore.Rewrite.Step".

The matching criterion returns a substitution which takes its argument to the
search goal (see 'matchWith'). The 'searchType' is used to restrict which states
may be considered for matching.

@searchGraph@ returns a list of substitutions which take the initial
configuration to the goal defined by the matching criterion. The number of
solutions returned is limited by 'bound'.

See also: 'Kore.Rewrite.Strategy.runStrategy', 'matchWith'
-}
searchGraph ::
    MonadSimplify m =>
    -- | Search options
    Config ->
    -- | Matching criterion
    (config -> MaybeT m substitution) ->
    -- | Execution tree
    Strategy.ExecutionGraph config rule ->
    m [substitution]
searchGraph Config{searchType, bound} match executionGraph = do
    let selectedConfigs = pick executionGraph
    matches <- catMaybes <$> traverse (runMaybeT . match) selectedConfigs
    return (Limit.takeWithin bound matches)
  where
    pick =
        case searchType of
            ONE -> Strategy.pickOne
            PLUS -> Strategy.pickPlus
            STAR -> Strategy.pickStar
            FINAL -> Strategy.pickFinal

matchWith ::
    forall m.
    MonadSimplify m =>
    SideCondition RewritingVariableName ->
    Pattern RewritingVariableName ->
    Pattern RewritingVariableName ->
    MaybeT m (OrCondition RewritingVariableName)
matchWith sideCondition e1 e2 = do
    matchResults <- MaybeT $ matchIncremental sideCondition t1 t2
    let mergeAndEvaluate ::
            MatchResult RewritingVariableName ->
            m (OrCondition RewritingVariableName)
        mergeAndEvaluate predSubst = do
            results <- Logic.observeAllT $ mergeAndEvaluateBranches predSubst
            return (MultiOr.make results)
        mergeAndEvaluateBranches ::
            MatchResult RewritingVariableName ->
            LogicT m (Condition RewritingVariableName)
        mergeAndEvaluateBranches (predicate, substitution) = do
            merged <-
                mergePredicatesAndSubstitutions
                    sideCondition
                    [ predicate
                    , Conditional.predicate e1
                    , Conditional.predicate e2
                    ]
                    [from @(Map.Map _ _) @(Substitution _) substitution]
            lift (SMT.evalConditional merged Nothing) >>= \case
                Nothing ->
                    mergePredicatesAndSubstitutions
                        sideCondition
                        [Conditional.predicate merged]
                        [Conditional.substitution merged]
                Just False -> return Condition.bottom
                Just True ->
                    Conditional.substitution merged
                        & Condition.fromSubstitution
                        & return
    results <- lift $ mergeAndEvaluate matchResults
    guardAgainstBottom results
    return results
  where
    t1 = Conditional.term e1
    t2 = Conditional.term e2
