{-|
Description : Rule index attribute
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Attribute.RuleIndex
    ( RuleIndex (..)
    , RuleIndexCase (..)
    ) where

import Prelude.Kore

import Data.Default
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug

data RuleIndexCase
    = AxiomIndex !Int
    | ClaimIndex !Int
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

{- | This attribute is used in the REPL for tagging
    and uniquely identifiying axioms and claims.
 -}
newtype RuleIndex = RuleIndex { getRuleIndex :: Maybe RuleIndexCase }
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Default RuleIndex where
    def = RuleIndex Nothing
