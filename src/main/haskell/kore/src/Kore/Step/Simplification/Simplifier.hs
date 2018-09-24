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
import Data.Reflection ( give )
import           Kore.AST.Common
import           Kore.AST.MetaOrObject
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.Function.Data
                 ( ApplicationFunctionEvaluator )
import           Kore.Step.Simplification.Data
                 ( PureMLPatternSimplifier (..) )
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplifyToOr )
import           Kore.Step.StepperAttributes

create
    ::  ( MetaOrObject level
        )
    => MetadataTools level StepperAttributes
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level Variable]
    -- ^ Map from symbol IDs to defined functions
    -> PureMLPatternSimplifier level Variable
create
    tools
    symbolIdToEvaluator
  = give (convertMetadataTools tools) $ 
    PureMLPatternSimplifier
        (Pattern.simplifyToOr tools symbolIdToEvaluator)
