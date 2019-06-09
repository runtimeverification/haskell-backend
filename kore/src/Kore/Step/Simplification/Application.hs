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

import qualified Kore.Attribute.Pattern as Attribute
import qualified Kore.Internal.MultiOr as MultiOr
                 ( fullCrossProduct, mergeAll )
import           Kore.Internal.OrPattern
                 ( OrPattern )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Conditional (..), Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Step.Function.Evaluator
                 ( evaluateApplication )
import           Kore.Step.Simplification.Data as Simplifier
import qualified Kore.Step.Simplification.Data as BranchT
                 ( gather )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Unparser
import           Kore.Variables.Fresh

type ExpandedApplication variable =
    Conditional
        variable
        (CofreeF
            (Application Symbol)
            (Attribute.Pattern variable)
            (TermLike variable)
        )

{-|'simplify' simplifies an 'Application' of 'OrPattern'.

To do that, it first distributes the terms, making it an Or of Application
patterns, each Application having 'Pattern's as children,
then it simplifies each of those.

Simplifying an Application of Pattern means merging the children
predicates ans substitutions, applying functions on the Application(terms),
then merging everything into an Pattern.
-}
simplify
    ::  ( Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => CofreeF
        (Application Symbol)
        (Attribute.Pattern variable)
        (OrPattern variable)
    -> simplifier (OrPattern variable)
simplify (valid :< app) = do
    evaluated <-
        traverse
            (makeAndEvaluateApplications valid symbol)
            -- The "Propagation Or" inference rule together with
            -- "Propagation Bottom" for the case when a child or is empty.
            (MultiOr.fullCrossProduct children)
    return (OrPattern.flatten evaluated)
  where
    Application
        { applicationSymbolOrAlias = symbol
        , applicationChildren = children
        }
      = app

makeAndEvaluateApplications
    ::  ( Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => Attribute.Pattern variable
    -> Symbol
    -> [Pattern variable]
    -> simplifier (OrPattern variable)
makeAndEvaluateApplications valid symbol children = do
    makeAndEvaluateSymbolApplications valid symbol children

makeAndEvaluateSymbolApplications
    ::  ( Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => Attribute.Pattern variable
    -> Symbol
    -> [Pattern variable]
    -> simplifier (OrPattern variable)
makeAndEvaluateSymbolApplications valid symbol children = do
    expandedApplications <-
        BranchT.gather $ makeExpandedApplication valid symbol children
    orResults <- traverse evaluateApplicationFunction expandedApplications
    return (MultiOr.mergeAll orResults)

evaluateApplicationFunction
    ::  ( Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => ExpandedApplication variable
    -- ^ The pattern to be evaluated
    -> simplifier (OrPattern variable)
evaluateApplicationFunction Conditional { term, predicate, substitution } =
    evaluateApplication
        Conditional { term = (), predicate, substitution }
        term

makeExpandedApplication
    ::  ( Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        , MonadSimplify simplifier
        )
    => Attribute.Pattern variable
    -> Symbol
    -> [Pattern variable]
    -> BranchT simplifier (ExpandedApplication variable)
makeExpandedApplication valid symbol children = do
    merged <-
        mergePredicatesAndSubstitutions
            (map Pattern.predicate children)
            (map Pattern.substitution children)
    let term =
            valid :< Application
                { applicationSymbolOrAlias = symbol
                , applicationChildren = Pattern.term <$> children
                }
    return $ Pattern.withCondition term merged
