{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.OrPattern (
    simplifyConditionsWithSmt,
) where

import Kore.Internal.Condition (
    Condition,
 )
import qualified Kore.Internal.Condition as Condition (
    bottom,
    fromPredicate,
    toPredicate,
 )
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import qualified Kore.Internal.Conditional as Conditional (
    Conditional (..),
 )
import qualified Kore.Internal.OrCondition as OrCondition
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern (
    splitTerm,
    withCondition,
 )
import Kore.Internal.Predicate (
    makeAndPredicate,
    makeNotPredicate,
    makeTruePredicate,
 )
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    toPredicate,
    top,
 )
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator (
    filterMultiOr,
 )
import Kore.Step.Simplification.Simplify (
    MonadSimplify,
    simplifyCondition,
 )
import Kore.TopBottom (
    TopBottom (..),
 )
import Logic (
    LogicT,
 )
import qualified Logic
import Prelude.Kore

simplifyConditionsWithSmt ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    OrPattern RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
simplifyConditionsWithSmt sideCondition unsimplified =
    OrPattern.observeAllT $ do
        unsimplified1 <- Logic.scatter unsimplified
        simplifyAndPrune unsimplified1
  where
    simplifyAndPrune ::
        Pattern RewritingVariableName ->
        LogicT simplifier (Pattern RewritingVariableName)
    simplifyAndPrune (Pattern.splitTerm -> (term, condition)) = do
        simplified <- simplifyCondition sideCondition condition
        filtered <-
            return simplified
                & resultWithFilter pruneCondition
                & resultWithFilter rejectCondition
                & lift
        return (term `Pattern.withCondition` filtered)

    resultWithFilter ::
        (Condition RewritingVariableName -> simplifier (Maybe Bool)) ->
        simplifier (Condition RewritingVariableName) ->
        simplifier (Condition RewritingVariableName)
    resultWithFilter conditionFilter previousResult = do
        previous <- previousResult
        if isTop previous || isBottom previous
            then return previous
            else do
                filtered <- conditionFilter previous
                case filtered of
                    Just True ->
                        -- TODO(virgil): We should be able to return
                        -- Condition.top, but if 'a' is the only constructor
                        -- of a sort and 'v' is a variable, then the SMT
                        -- can detect that 'not v=a' is not satisfiable
                        -- so we may remove a substitution here. However,
                        -- we are not able to handle that properly.
                        return
                            previous
                                { Conditional.predicate = makeTruePredicate
                                }
                    Just False -> return Condition.bottom
                    Nothing -> return previous
    pruneCondition :: Condition RewritingVariableName -> simplifier (Maybe Bool)
    pruneCondition condition = do
        implicationNegation <-
            makeAndPredicate
                sidePredicate
                (makeNotPredicate $ Condition.toPredicate condition)
                & Condition.fromPredicate
                & simplifyCondition SideCondition.top
                & OrCondition.observeAllT
        filteredConditions <- SMT.Evaluator.filterMultiOr implicationNegation
        if isTop filteredConditions
            then return (Just False)
            else
                if isBottom filteredConditions
                    then return (Just True)
                    else return Nothing

    rejectCondition :: Condition RewritingVariableName -> simplifier (Maybe Bool)
    rejectCondition condition = do
        simplifiedConditions <-
            simplifyCondition SideCondition.top (addPredicate condition)
                & OrCondition.observeAllT
        filteredConditions <- SMT.Evaluator.filterMultiOr simplifiedConditions
        if isBottom filteredConditions
            then return (Just False)
            else
                if isTop filteredConditions
                    then return (Just True)
                    else return Nothing

    sidePredicate = SideCondition.toPredicate sideCondition

    addPredicate ::
        Conditional RewritingVariableName term ->
        Conditional RewritingVariableName term
    addPredicate c@Conditional{predicate} =
        c{Conditional.predicate = makeAndPredicate predicate sidePredicate}
