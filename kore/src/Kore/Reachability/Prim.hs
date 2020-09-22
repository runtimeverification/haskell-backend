{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Reachability.Prim
    ( Prim (..)
    ) where

import Prelude.Kore

import Pretty

{- | The primitive transitions of the reachability proof strategy.
 -}
data Prim
    = Begin
    -- ^ The start of each proof step
    | Simplify
    | CheckImplication
    -- ^ Check if the claim's implication is valid.
    | ApplyClaims
    | ApplyAxioms
    deriving (Show)

instance Pretty Prim where
    pretty Begin = "begin proof step"
    pretty Simplify = "simplify the claim"
    pretty CheckImplication = "check implication"
    pretty ApplyClaims = "apply claims"
    pretty ApplyAxioms = "apply axioms"
