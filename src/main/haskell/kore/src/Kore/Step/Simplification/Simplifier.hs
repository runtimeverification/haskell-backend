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

import           Kore.AST.Pure
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.Function.Data
                 ( BuiltinAndAxiomsFunctionEvaluator )
import           Kore.Step.Simplification.Data
                 ( StepPatternSimplifier (..) )
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplifyToOr )
import           Kore.Step.StepperAttributes
                 ( StepperAttributes )
import           Kore.Unparser
import           Kore.Variables.Fresh

create
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => MetadataTools level StepperAttributes
    -> Map.Map (Id level) (BuiltinAndAxiomsFunctionEvaluator level)
    -- ^ Map from symbol IDs to defined functions
    -> StepPatternSimplifier level variable
create
    tools
    symbolIdToEvaluator
  =
    StepPatternSimplifier
        (Pattern.simplifyToOr tools symbolIdToEvaluator)
