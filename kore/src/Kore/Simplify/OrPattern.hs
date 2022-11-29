{-# LANGUAGE TemplateHaskell #-}

{- |
Copyright   : (c) Runtime Verification, 2018-2021
License     : BSD-3-Clause
-}
module Kore.Simplify.OrPattern (
    simplifyConditionsWithSmt,
) where

import Kore.Internal.Condition (
    Condition,
 )
import Kore.Internal.Condition qualified as Condition (
    bottom,
    fromPredicate,
    toPredicate,
 )
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import Kore.Internal.Conditional qualified as Conditional (
    Conditional (..),
 )
import Kore.Internal.OrCondition qualified as OrCondition
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern (
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
import Kore.Internal.SideCondition qualified as SideCondition (
    toPredicate,
    top,
 )
import Kore.Log.DecidePredicateUnknown (srcLoc)
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Rewrite.SMT.Evaluator qualified as SMT.Evaluator (
    filterMultiOr,
 )
import Kore.Simplify.Simplify (
    Simplifier,
    liftSimplifier,
    simplifyCondition,
 )
import Kore.TopBottom (
    TopBottom (..),
 )
import Logic (
    LogicT,
 )
import Logic qualified
import Prelude.Kore

simplifyConditionsWithSmt ::
    SideCondition RewritingVariableName ->
    OrPattern RewritingVariableName ->
    Simplifier (OrPattern RewritingVariableName)
simplifyConditionsWithSmt sideCondition unsimplified =
    OrPattern.observeAllT $ do
        unsimplified1 <- Logic.scatter unsimplified
        simplifyAndPrune unsimplified1
  where
    simplifyAndPrune ::
        Pattern RewritingVariableName ->
        LogicT Simplifier (Pattern RewritingVariableName)
    simplifyAndPrune (Pattern.splitTerm -> (term, condition)) = do
        simplified <- simplifyCondition sideCondition condition
        filtered <-
            return simplified
                & resultWithFilter pruneCondition
                & resultWithFilter rejectCondition
                & lift
        return (term `Pattern.withCondition` filtered)

    resultWithFilter ::
        (Condition RewritingVariableName -> Simplifier (Maybe Bool)) ->
        Simplifier (Condition RewritingVariableName) ->
        Simplifier (Condition RewritingVariableName)
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
    pruneCondition :: Condition RewritingVariableName -> Simplifier (Maybe Bool)
    pruneCondition condition = do
        implicationNegation <-
            makeAndPredicate
                sidePredicate
                (makeNotPredicate $ Condition.toPredicate condition)
                & Condition.fromPredicate
                & simplifyCondition SideCondition.top
                & OrCondition.observeAllT
        filteredConditions <-
            liftSimplifier $
                SMT.Evaluator.filterMultiOr $srcLoc implicationNegation
        if isTop filteredConditions
            then return (Just False)
            else
                if isBottom filteredConditions
                    then return (Just True)
                    else return Nothing

    rejectCondition :: Condition RewritingVariableName -> Simplifier (Maybe Bool)
    rejectCondition condition = do
        simplifiedConditions <-
            simplifyCondition SideCondition.top (addPredicate condition)
                & OrCondition.observeAllT
        filteredConditions <-
            liftSimplifier $
                SMT.Evaluator.filterMultiOr $srcLoc simplifiedConditions
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
