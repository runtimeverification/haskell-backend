{- |
Copyright : (c) Runtime Verification 2021
License   : BSD-3-Clause
-}
module Kore.Log.Warning (
    -- * WarnZ3Crash
    WarnZ3Crash,
    warnZ3Crash,
) where

import Control.Exception (
    displayException,
 )
import Log (
    MonadLog (..),
 )
import Log.Entry (
    Entry (..),
    Severity (Warning),
 )
import Prelude.Kore
import Pretty (
    Pretty,
    indent,
    pretty,
    vsep,
 )
import SMT.SimpleSMT (
    SolverException,
 )

-- | Warn user when Z3 has crashed and been restarted
newtype WarnZ3Crash = WarnZ3Crash {unWarnZ3Crash :: SolverException}
    deriving stock (Show)

instance Pretty WarnZ3Crash where
    pretty (WarnZ3Crash e) =
        vsep
            [ "Z3 crashed with error:"
            , indent 4 $ pretty $ displayException e
            , "Restarting Z3."
            ]

instance Entry WarnZ3Crash where
    entrySeverity _ = Warning
    oneLineDoc _ = "Z3 crashed. Restarting."
    helpDoc _ =
        "Warn when Z3 has crashed. It will be restarted automatically \
        \only once."

-- | Log warning for Z3 crash
warnZ3Crash :: MonadLog m => SolverException -> m ()
warnZ3Crash = logEntry . WarnZ3Crash
