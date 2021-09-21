{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Log.WarnDepthLimitExceeded (
    WarnDepthLimitExceeded (..),
    warnDepthLimitExceeded,
) where

import Debug
import Log
import Numeric.Natural (
    Natural,
 )
import Prelude.Kore
import Pretty (
    Pretty,
    pretty,
 )
import qualified Pretty

newtype WarnDepthLimitExceeded = WarnDepthLimitExceeded {limitExceeded :: Natural}
    deriving stock (Show, Eq)

instance Debug WarnDepthLimitExceeded where
    debugPrec w = \_ -> Pretty.pretty . show $ w

instance Diff WarnDepthLimitExceeded where
    diffPrec = diffPrecEq
instance Pretty WarnDepthLimitExceeded where
    pretty (WarnDepthLimitExceeded n) =
        Pretty.hsep
            ["The depth limit", pretty n, "was exceeded."]

instance Entry WarnDepthLimitExceeded where
    entrySeverity _ = Warning
    oneLineDoc (WarnDepthLimitExceeded limitExceeded) =
        Pretty.pretty limitExceeded
    helpDoc _ = "warn when depth limit is exceeded"

warnDepthLimitExceeded :: MonadLog log => Natural -> log ()
warnDepthLimitExceeded = logEntry . WarnDepthLimitExceeded
