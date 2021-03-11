{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.WarnDepthLimitExceeded
    ( WarnDepthLimitExceeded (..)
    , warnDepthLimitExceeded
    ) where

import Prelude.Kore

import Log
import Pretty
    ( Pretty
    , pretty
    )
import qualified Pretty
import Numeric.Natural
    ( Natural
    )

newtype WarnDepthLimitExceeded =
    WarnDepthLimitExceeded { limitExceeded :: Natural }
    deriving Show

instance Pretty WarnDepthLimitExceeded where
    pretty (WarnDepthLimitExceeded n) =
        Pretty.vsep
            [ "The depth limit", pretty n, "was exceeded."]

instance Entry WarnDepthLimitExceeded where
    entrySeverity _ = Warning
    helpDoc _ = "warn when depth limit is exceeded"

warnDepthLimitExceeded :: MonadLog log => Natural -> log ()
warnDepthLimitExceeded = logEntry . WarnDepthLimitExceeded