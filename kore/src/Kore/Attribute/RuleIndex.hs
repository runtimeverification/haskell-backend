{- |
Description : Rule index attribute
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
-}
module Kore.Attribute.RuleIndex (
    RuleIndex (..),
    RuleIndexCase (..),
) where

import Data.Default
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Debug
import Prelude.Kore

data RuleIndexCase
    = AxiomIndex !Int
    | ClaimIndex !Int
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

{- | This attribute is used in the REPL for tagging
    and uniquely identifiying axioms and claims.
-}
newtype RuleIndex = RuleIndex {getRuleIndex :: Maybe RuleIndexCase}
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Default RuleIndex where
    def = RuleIndex Nothing
