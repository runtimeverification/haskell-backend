module Kore.Log.Warning (
    -- * WarnZ3Crash
    WarnZ3Crash,
    warnZ3Crash,
) where

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
    pretty,
 )

-- | Warn user when Z3 has crashed and been restarted
data WarnZ3Crash = WarnZ3Crash
    deriving stock (Show)

instance Pretty WarnZ3Crash where
    pretty = pretty . show

instance Entry WarnZ3Crash where
    entrySeverity _ = Warning
    oneLineDoc = pretty
    helpDoc _ =
        "Warn when Z3 has crashed. It will be restarted automatically \
        \only once."

-- | Log warning for Z3 crash
warnZ3Crash :: MonadLog m => m ()
warnZ3Crash = logEntry WarnZ3Crash
