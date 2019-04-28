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
                 ( SmtMetadataTools )
import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Simplification.Data
                 ( TermLikeSimplifier, termLikeSimplifier )
import qualified Kore.Step.Simplification.TermLike as TermLike
                 ( simplifyToOr )

create
    ::  ( MetaOrObject level )
    => SmtMetadataTools StepperAttributes
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLikeSimplifier level
create
    tools
    axiomIdToEvaluator
  =
    termLikeSimplifier
        (TermLike.simplifyToOr tools axiomIdToEvaluator)
