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

import           Kore.AST.Pure
import           Kore.Attribute.Symbol
                 ( StepperAttributes )
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Simplification.Data
                 ( StepPatternSimplifier, stepPatternSimplifier )
import qualified Kore.Step.Simplification.Pattern as Pattern
                 ( simplifyToOr )

create
    ::  ( MetaOrObject level )
    => MetadataTools level StepperAttributes
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> StepPatternSimplifier level
create
    tools
    axiomIdToEvaluator
  =
    stepPatternSimplifier
        (Pattern.simplifyToOr tools axiomIdToEvaluator)
