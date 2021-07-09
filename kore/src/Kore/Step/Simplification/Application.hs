{- |
Module      : Kore.Step.Simplification.Application
Description : Tools for Application pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Application (
    simplify,
    Application (..),
) where

import Control.Monad.Catch (
    MonadThrow,
 )
import Kore.Attribute.Synthetic (synthesize)
import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Conditional (..),
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition (
    SideCondition,
 )
import qualified Kore.Internal.SideCondition as SideCondition
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Function.Evaluator (
    evaluateApplication,
 )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Substitution (
    mergePredicatesAndSubstitutions,
 )
import Logic (
    LogicT,
 )
import qualified Logic
import Prelude.Kore

type ExpandedApplication variable =
    Conditional variable (Application Symbol (TermLike variable))

{- |'simplify' simplifies an 'Application' of 'OrPattern'.

To do that, it first distributes the terms, making it an Or of Application
patterns, each Application having 'Pattern's as children,
then it simplifies each of those.

Simplifying an Application of Pattern means merging the children
predicates ans substitutions, applying functions on the Application(terms),
then merging everything into an Pattern.
-}
simplify ::
    MonadSimplify simplifier =>
    MonadThrow simplifier =>
    SideCondition RewritingVariableName ->
    Application Symbol (OrPattern RewritingVariableName) ->
    simplifier (OrPattern RewritingVariableName)
simplify sideCondition application = do
    evaluated <- OrPattern.observeAllT $ do
        Application{applicationChildren = result} <-
            Logic.scatter childrenCrossProduct
        lift $ makeAndEvaluateApplications sideCondition symbol result
    return (OrPattern.flatten evaluated)
  where
    Application
        { applicationSymbolOrAlias = symbol
        } =
            application

    -- The "Propagation Or" inference rule together with
    -- "Propagation Bottom" for the case when a child or is empty.
    childrenCrossProduct =
        MultiOr.distributeApplication application

makeAndEvaluateApplications ::
    MonadSimplify simplifier =>
    MonadThrow simplifier =>
    SideCondition RewritingVariableName ->
    Symbol ->
    [Pattern RewritingVariableName] ->
    simplifier (OrPattern RewritingVariableName)
makeAndEvaluateApplications =
    makeAndEvaluateSymbolApplications

makeAndEvaluateSymbolApplications ::
    MonadSimplify simplifier =>
    MonadThrow simplifier =>
    SideCondition RewritingVariableName ->
    Symbol ->
    [Pattern RewritingVariableName] ->
    simplifier (OrPattern RewritingVariableName)
makeAndEvaluateSymbolApplications sideCondition symbol children = do
    expandedApplications <-
        makeExpandedApplication sideCondition symbol children
            & Logic.observeAllT
    orResults <-
        traverse
            (evaluateApplicationFunction sideCondition)
            expandedApplications
    return (MultiOr.mergeAll orResults)

{- | Evaluates function applications, without attempting
 to reevaluate functions which are known to have been simplified
 as much as possible inside the current rewrite step.
-}
evaluateApplicationFunction ::
    MonadSimplify simplifier =>
    MonadThrow simplifier =>
    -- | The predicate from the configuration
    SideCondition RewritingVariableName ->
    -- | The pattern to be evaluated
    ExpandedApplication RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
evaluateApplicationFunction
    sideCondition
    expandedApp@Conditional{term, predicate, substitution}
        | SideCondition.isSimplifiedFunction term sideCondition =
            let applicationPattern =
                    synthesize . ApplySymbolF <$> expandedApp
             in applicationPattern
                    & Pattern.markSimplified
                    & OrPattern.fromPattern
                    & return
        | otherwise =
            evaluateApplication
                sideCondition
                Conditional{term = (), predicate, substitution}
                term

makeExpandedApplication ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Symbol ->
    [Pattern RewritingVariableName] ->
    LogicT simplifier (ExpandedApplication RewritingVariableName)
makeExpandedApplication sideCondition symbol children = do
    merged <-
        mergePredicatesAndSubstitutions
            sideCondition
            (fmap Pattern.predicate children)
            (fmap Pattern.substitution children)
    let term =
            symbolApplication
                symbol
                (fmap Pattern.term children)

    return $ Conditional.withCondition term merged
