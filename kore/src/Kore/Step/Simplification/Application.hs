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

import Branch
    ( BranchT
    )
import qualified Branch as Branch
import Kore.Internal.Condition as Condition
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
import Kore.Internal.TermLike
import qualified Kore.Profiler.Profile as Profile
    ( simplificationBranching
    )
import Kore.Step.Function.Evaluator
    ( evaluateApplication
    )
import Kore.Step.Simplification.Simplify as Simplifier
import Kore.Step.Substitution
    ( mergePredicatesAndSubstitutions
    )

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
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Condition variable
    -> Application Symbol (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify predicate application = do
    evaluated <-
        traverse
            (makeAndEvaluateApplications predicate symbol)
            childrenCrossProduct
    let result = OrPattern.flatten evaluated
    Profile.simplificationBranching
        "Application"
        (symbolConstructor symbol)
        (length childrenCrossProduct)
        (length result)
    return result
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
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Condition variable
    -> Symbol
    -> [Pattern variable]
    -> simplifier (OrPattern variable)
makeAndEvaluateApplications =
    makeAndEvaluateSymbolApplications

makeAndEvaluateSymbolApplications
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Condition variable
    -> Symbol
    -> [Pattern variable]
    -> simplifier (OrPattern variable)
makeAndEvaluateSymbolApplications predicate symbol children = do
    expandedApplications <-
        Branch.gather $ makeExpandedApplication symbol children
    orResults <- traverse
        (evaluateApplicationFunction predicate)
        expandedApplications
    return (MultiOr.mergeAll orResults)

evaluateApplicationFunction
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Condition variable
    -- ^ The predicate from the configuration
    -> ExpandedApplication variable
    -- ^ The pattern to be evaluated
    -> simplifier (OrPattern variable)
evaluateApplicationFunction
    configurationCondition
    Conditional { term, predicate, substitution }
  =
    evaluateApplication
        configurationCondition
        Conditional { term = (), predicate, substitution }
        term

makeExpandedApplication
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Symbol
    -> [Pattern variable]
    -> BranchT simplifier (ExpandedApplication variable)
makeExpandedApplication symbol children = do
    merged <-
        mergePredicatesAndSubstitutions
            (map Pattern.predicate children)
            (map Pattern.substitution children)
    let term = symbolApplication symbol (Pattern.term <$> children)

    return $ Conditional.withCondition term merged
