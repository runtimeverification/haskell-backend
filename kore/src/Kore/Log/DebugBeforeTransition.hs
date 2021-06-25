{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.DebugBeforeTransition (
    DebugBeforeTransition (..),
    debugBeforeTransition,
) where

import Kore.Reachability.ClaimState (
    ClaimState,
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

data DebugBeforeTransition = DebugBeforeTransition
    { proofState :: ClaimState SomeClaim
    , transition :: Prim
    }
    deriving stock (Show)

instance Pretty DebugBeforeTransition where
    pretty
        DebugBeforeTransition
            { proofState
            , transition
            } =
            Pretty.vsep
                [ "Reached proof state with the following configuration:"
                , Pretty.indent 4 (pretty proofState)
                , "To which the following transition will be applied:"
                , Pretty.indent 4 (pretty transition)
                ]

instance Entry DebugBeforeTransition where
    entrySeverity _ = Debug
    helpDoc _ = "log proof state"
    oneLineDoc = Just . pretty . transition

debugBeforeTransition ::
    MonadLog log =>
    ClaimState SomeClaim ->
    Prim ->
    log ()
debugBeforeTransition proofState transition =
    logEntry DebugBeforeTransition{proofState, transition}
