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

import           Kore.Step.Axiom.Data
                 ( BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Simplification.Data
                 ( TermLikeSimplifier, termLikeSimplifier )
import qualified Kore.Step.Simplification.TermLike as TermLike
                 ( simplifyToOr )

create
    :: BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLikeSimplifier
create axiomIdToEvaluator =
    termLikeSimplifier (TermLike.simplifyToOr axiomIdToEvaluator)
