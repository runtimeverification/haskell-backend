{-|
Module      : Kore.Simplification.ExpandedPattern
Description : Tools for ExpandedPattern simplification.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Simplification.ExpandedPattern
    ( simplify
    ) where

import qualified Data.Map as Map

import           Kore.AST.Common
                 ( Id, SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern (ExpandedPattern),
                 PredicateSubstitution (PredicateSubstitution) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( ExpandedPattern (..) )
import qualified Kore.Step.ExpandedPattern as PredicateSubstitution
                 ( PredicateSubstitution (..) )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator )
import qualified Kore.Step.Merging.ExpandedPattern as ExpandedPattern
                 ( mergeWithPredicateSubstitution )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( traverseWithPairs )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier (..), SimplificationProof (..),
                 Simplifier )
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplifyToOr )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Int
                 ( IntVariable (..) )

{-| Simplifies an 'ExpandedPattern', returning an 'OrOfExpandedPattern'.
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
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level variable]
    -- ^ Map from symbol IDs to defined functions
    -> ExpandedPattern level domain variable
    -> Simplifier
        ( OrOfExpandedPattern level domain variable
        , SimplificationProof level
        )
simplify
    tools
    symbolIdToEvaluator
    ExpandedPattern {term, predicate, substitution}
  = do
    (simplifiedTerm, _)
        <- Pattern.simplifyToOr tools symbolIdToEvaluator term
    (simplifiedPatt, _) <-
        OrOfExpandedPattern.traverseWithPairs
            (ExpandedPattern.mergeWithPredicateSubstitution
                tools
                -- TODO: refactor.
                (PureMLPatternSimplifier
                    (Pattern.simplifyToOr tools symbolIdToEvaluator))
                PredicateSubstitution
                    { predicate = predicate
                    , substitution = substitution
                    }
            )
            simplifiedTerm
    return (simplifiedPatt, SimplificationProof)
