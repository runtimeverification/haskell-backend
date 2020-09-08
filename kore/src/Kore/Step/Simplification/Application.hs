{-|
Module      : Kore.Step.Simplification.Application
Description : Tools for Application pattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.Application
    ( simplify
    , Application (..)
    ) where

import Control.Monad.Catch
    ( MonadThrow
    )
import Prelude.Kore

import qualified Kore.Internal.Conditional as Conditional
import qualified Kore.Internal.MultiOr as MultiOr
    ( fullCrossProduct
    , mergeAll
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Conditional (..)
    , Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Internal.TermLike
import Kore.Step.Function.Evaluator
    ( evaluateApplication
    )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Substitution
    ( mergePredicatesAndSubstitutions
    )
import Logic
    ( LogicT
    )
import qualified Logic

type ExpandedApplication variable =
    Conditional variable (Application Symbol (TermLike variable))

{-|'simplify' simplifies an 'Application' of 'OrPattern'.

To do that, it first distributes the terms, making it an Or of Application
patterns, each Application having 'Pattern's as children,
then it simplifies each of those.

Simplifying an Application of Pattern means merging the children
predicates ans substitutions, applying functions on the Application(terms),
then merging everything into an Pattern.
-}
simplify
    ::  ( InternalVariable variable
        , MonadSimplify simplifier
        , MonadThrow simplifier
        )
    => SideCondition variable
    -> Application Symbol (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify sideCondition application = do
    evaluated <-
        traverse
            (makeAndEvaluateApplications sideCondition symbol)
            childrenCrossProduct
    return (OrPattern.flatten evaluated)
  where
    Application
        { applicationSymbolOrAlias = symbol
        , applicationChildren = children
        }
      = application

    -- The "Propagation Or" inference rule together with
    -- "Propagation Bottom" for the case when a child or is empty.
    childrenCrossProduct = MultiOr.fullCrossProduct children

makeAndEvaluateApplications
    ::  ( InternalVariable variable
        , MonadSimplify simplifier
        , MonadThrow simplifier
        )
    => SideCondition variable
    -> Symbol
    -> [Pattern variable]
    -> simplifier (OrPattern variable)
makeAndEvaluateApplications =
    makeAndEvaluateSymbolApplications

makeAndEvaluateSymbolApplications
    ::  ( InternalVariable variable
        , MonadSimplify simplifier
        , MonadThrow simplifier
        )
    => SideCondition variable
    -> Symbol
    -> [Pattern variable]
    -> simplifier (OrPattern variable)
makeAndEvaluateSymbolApplications sideCondition symbol children = do
    expandedApplications <-
        makeExpandedApplication sideCondition symbol children
        & Logic.observeAllT
    orResults <-
        traverse
            (evaluateApplicationFunction sideCondition)
            expandedApplications
    return (MultiOr.mergeAll orResults)

evaluateApplicationFunction
    ::  ( InternalVariable variable
        , MonadSimplify simplifier
        , MonadThrow simplifier
        )
    => SideCondition variable
    -- ^ The predicate from the configuration
    -> ExpandedApplication variable
    -- ^ The pattern to be evaluated
    -> simplifier (OrPattern variable)
evaluateApplicationFunction
    sideCondition
    Conditional { term, predicate, substitution }
  =
    evaluateApplication
        sideCondition
        Conditional { term = (), predicate, substitution }
        term

makeExpandedApplication
    :: (InternalVariable variable, MonadSimplify simplifier)
    => SideCondition variable
    -> Symbol
    -> [Pattern variable]
    -> LogicT simplifier (ExpandedApplication variable)
makeExpandedApplication sideCondition symbol children = do
    merged <-
        mergePredicatesAndSubstitutions
            sideCondition
            (map Pattern.predicate children)
            (map Pattern.substitution children)
    let term = symbolApplication symbol (Pattern.term <$> children)

    return $ Conditional.withCondition term merged
