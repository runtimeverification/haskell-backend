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
    ) where

import qualified Data.Map as Map

import           Kore.AST.Common
                 ( Application (..), Id, SortedVariable, SymbolOrAlias )
import           Kore.AST.MetaOrObject
import           Kore.AST.PureML
                 ( PureMLPattern )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Predicate.Predicate
                 ( Predicate )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern,
                 PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import qualified Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator (..) )
import           Kore.Step.Function.Evaluator
                 ( evaluateApplication )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( fullCrossProduct, traverseFlattenWithPairsGeneric )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier (..), SimplificationProof (..),
                 Simplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Step.Substitution
                 ( mergePredicatesAndSubstitutions )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Unification.Unifier
                 ( UnificationSubstitution )
import           Kore.Variables.Int
                 ( IntVariable (..) )

data ExpandedApplication level variable = ExpandedApplication
    { term         :: !(Application level (PureMLPattern level variable))
    , predicate    :: !(Predicate level variable)
    , substitution :: !(UnificationSubstitution level variable)
    }
    deriving (Eq, Show)

{-|'simplify' simplifies an 'Application' of 'OrOfExpandedPattern'.

To do that, it first distributes the terms, making it an Or of Application
patterns, each Application having 'ExpandedPattern's as children,
then it simplifies each of those.

Simplifying an Application of ExpandedPattern means merging the children
predicates ans substitutions, applying functions on the Application(terms),
then merging everything into an ExpandedPattern.
-}
simplify
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPatternSimplifier level variable
    -- ^ Evaluates functions.
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level variable]
    -- ^ Map from symbol IDs to defined functions
    -> Application level (OrOfExpandedPattern level variable)
    -> Simplifier
        ( OrOfExpandedPattern level variable
        , SimplificationProof level
        )
simplify
    tools
    simplifier
    symbolIdToEvaluator
    Application
        { applicationSymbolOrAlias = symbol
        , applicationChildren = children
        }
  = do
    let
        -- The "Propagation Or" inference rule together with
        -- "Propagation Bottom" for the case when a child or is empty.
        orDistributedChildren = OrOfExpandedPattern.fullCrossProduct children
    (unflattenedOr, _proofs) <-
        OrOfExpandedPattern.traverseFlattenWithPairsGeneric
            (makeAndEvaluateApplications
                tools simplifier symbolIdToEvaluator
                symbol
            )
            orDistributedChildren
    return
        ( unflattenedOr
        , SimplificationProof
        )

makeAndEvaluateApplications
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPatternSimplifier level variable
    -- ^ Evaluates functions.
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level variable]
    -- ^ Map from symbol IDs to defined functions
    -> SymbolOrAlias level
    -> [ExpandedPattern level variable]
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
makeAndEvaluateApplications
    tools
    simplifier
    symbolIdToEvaluator
    symbol
    children
  = do
    (expandedApplication, _proof) <-
        makeExpandedApplication tools symbol children
    (functionApplication, _proof) <-
        evaluateApplicationFunction
            tools simplifier symbolIdToEvaluator
            expandedApplication
    return (functionApplication, SimplificationProof)

evaluateApplicationFunction
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> PureMLPatternSimplifier level variable
    -- ^ Evaluates functions.
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level variable]
    -- ^ Map from symbol IDs to defined functions
    -> ExpandedApplication level variable
    -- ^ The pattern to be evaluated
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
evaluateApplicationFunction
    tools
    simplifier
    symbolIdToEvaluator
    ExpandedApplication
        { term, predicate, substitution }
  =
    evaluateApplication
        tools
        simplifier
        symbolIdToEvaluator
        PredicateSubstitution
            { predicate = predicate
            , substitution = substitution
            }
        term

makeExpandedApplication
    ::  ( MetaOrObject level
        , Kore.AST.Common.SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Ord (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , IntVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> SymbolOrAlias level
    -> [ExpandedPattern level variable]
    -> Simplifier
        (ExpandedApplication level variable, SimplificationProof level)
makeExpandedApplication tools symbol children
  = do
    (   PredicateSubstitution
            { predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , _proof) <-
            mergePredicatesAndSubstitutions
                tools
                (map ExpandedPattern.predicate children)
                (map ExpandedPattern.substitution children)
    return
        ( ExpandedApplication
            { term = Application
                { applicationSymbolOrAlias = symbol
                , applicationChildren = map ExpandedPattern.term children
                }
            , predicate = mergedPredicate
            , substitution = mergedSubstitution
            }
        , SimplificationProof
        )
