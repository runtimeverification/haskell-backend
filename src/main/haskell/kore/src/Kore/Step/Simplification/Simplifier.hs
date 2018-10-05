{-|
Module      : Kore.Step.Simplification.Simplifier
Description : Builds a simplifier.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}

module Kore.Step.Simplification.Simplifier
    ( create
    , createPredicateSimplifier
    ) where

import qualified Data.Map as Map

import           Kore.AST.Common
                 ( Id, SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator )
import           Kore.Step.Simplification.Data
                 ( MonadPureMLPatternSimplifier (MonadPureMLPatternSimplifier),
                 PredicateSimplifier, PureMLPatternSimplifier )
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplifyToOr )
import qualified Kore.Step.Simplification.Predicate as Predicate
                 ( monadSimplifier )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes (..) )
import           Kore.Substitution.Class
                 ( Hashable )
import           Kore.Variables.Fresh

create
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable Meta)
        , Show (variable Object)
        , FreshVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level variable]
    -- ^ Map from symbol IDs to defined functions
    -> PureMLPatternSimplifier level
create
    tools
    symbolIdToEvaluator
  =
    MonadPureMLPatternSimplifier
        (Pattern.simplifyToOr tools symbolIdToEvaluator)

-- TODO: Is this ever used?
createPredicateSimplifier
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Ord (variable Meta)
        , Ord (variable Object)
        , Show (variable Meta)
        , Show (variable Object)
        , FreshVariable variable
        , Hashable variable
        )
    => MetadataTools level StepperAttributes
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level variable]
    -> PredicateSimplifier level
createPredicateSimplifier tools symbolIdToEvaluator =
    Predicate.monadSimplifier (create tools symbolIdToEvaluator)
