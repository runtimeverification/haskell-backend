module Kore.Log.DebugBeginClaim (
    DebugBeginClaim (..),
    debugBeginClaim,
) where

import Kore.Reachability.SomeClaim (
    SomeClaim (..),
 )
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified Pretty

newtype DebugBeginClaim = DebugBeginClaim {claim :: SomeClaim}
    deriving stock (Show)

instance Pretty DebugBeginClaim where
    pretty DebugBeginClaim{claim} =
        Pretty.vsep ["Begin proof of claim:", Pretty.indent 4 (pretty claim)]

instance Entry DebugBeginClaim where
    entrySeverity _ = Debug
    helpDoc _ = "log starting claims"

debugBeginClaim ::
    MonadLog log =>
    SomeClaim ->
    log ()
debugBeginClaim claim = logEntry (DebugBeginClaim claim)
