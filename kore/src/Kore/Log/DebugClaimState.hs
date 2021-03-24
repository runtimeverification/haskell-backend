{-# LANGUAGE Strict #-}

{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.DebugClaimState (
    DebugClaimState (..),
) where

import Kore.Reachability.ClaimState (
    ClaimState (..),
 )
import Kore.Reachability.Prim (
    Prim (..),
 )
import Kore.Reachability.SomeClaim (
    SomeClaim (..),
 )
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified Pretty

data DebugClaimState = DebugClaimState
    { proofState :: ClaimState SomeClaim
    , transition :: Prim
    , result :: Maybe (ClaimState SomeClaim)
    }
    deriving (Show)

instance Pretty DebugClaimState where
    pretty
        DebugClaimState
            { proofState
            , transition
            , result
            } =
            Pretty.vsep
                [ "Reached proof state with the following configuration:"
                , Pretty.indent 4 (pretty proofState)
                , "On which the following transition applies:"
                , Pretty.indent 4 (pretty transition)
                , "Resulting in:"
                , Pretty.indent 4 (maybe "Terminal state." pretty result)
                ]

instance Entry DebugClaimState where
    entrySeverity _ = Debug
    helpDoc _ = "log proof state"
