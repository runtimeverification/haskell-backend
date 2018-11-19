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
    ) where

import qualified Data.Map as Map

import           Kore.AST.Common
                 ( Id, SortedVariable )
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.Function.Data
                 ( BuiltinAndAxiomsFunctionEvaluator )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier (..) )
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplifyToOr )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
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
    -> Map.Map (Id level) (BuiltinAndAxiomsFunctionEvaluator level)
    -- ^ Map from symbol IDs to defined functions
    -> PureMLPatternSimplifier level variable
create
    tools
    symbolIdToEvaluator
  =
    PureMLPatternSimplifier
        (Pattern.simplifyToOr tools symbolIdToEvaluator)
