{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Reachability.Prim (
    Prim (..),
) where

import Prelude.Kore
import Pretty

-- | The primitive transitions of the reachability proof strategy.
data Prim
    = -- | The start of each proof step
      Begin
    | Simplify
    | -- | Check if the claim's implication is valid.
      CheckImplication
    | ApplyClaims
    | ApplyAxioms
    deriving stock (Show)

instance Pretty Prim where
    pretty Begin = "begin proof step"
    pretty Simplify = "simplify the claim"
    pretty CheckImplication = "check implication"
    pretty ApplyClaims = "apply claims"
    pretty ApplyAxioms = "apply axioms"
