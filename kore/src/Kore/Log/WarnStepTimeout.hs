{-# LANGUAGE NoStrict #-}
{-# LANGUAGE NoStrictData #-}

{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause
-}
module Kore.Log.WarnStepTimeout (WarnStepTimeout (..), warnStepTimeout) where

import Log
import Prelude.Kore
import Pretty (Pretty)
import Pretty qualified

-- | @WarnStepTimeout@ is emitted when a step timed out.
newtype WarnStepTimeout = WarnStepTimeout Int
    deriving stock (Show)

instance Pretty WarnStepTimeout where
    pretty (WarnStepTimeout st) =
        Pretty.hsep
            [ "Step timed out. Timeout is currently set to"
            , Pretty.pretty st
            , "seconds."
            ]

instance Entry WarnStepTimeout where
    entrySeverity _ = Warning

    oneLineDoc _ = "WarnStepTimeout"

    helpDoc _ = "warn when a step has timed out"

warnStepTimeout :: MonadLog log => Int -> log ()
warnStepTimeout = logEntry . WarnStepTimeout
