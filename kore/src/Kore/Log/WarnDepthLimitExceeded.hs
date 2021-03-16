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
import Numeric.Natural
    ( Natural
    )
import Pretty
    ( Pretty
    , pretty
    )
import qualified Pretty
import Debug

newtype WarnDepthLimitExceeded =
    WarnDepthLimitExceeded { limitExceeded :: Natural }
    deriving (Show, Eq)

instance Debug WarnDepthLimitExceeded where
    debugPrec w = \_ -> Pretty.pretty . show $ w 

instance Diff WarnDepthLimitExceeded where
    diffPrec = diffPrecEq
instance Pretty WarnDepthLimitExceeded where
    pretty (WarnDepthLimitExceeded n) =
        Pretty.hsep
            [ "The depth limit", pretty n, "was exceeded."]

instance Entry WarnDepthLimitExceeded where
    entrySeverity _ = Warning
    helpDoc _ = "warn when depth limit is exceeded"

warnDepthLimitExceeded :: MonadLog log => Natural -> log ()
warnDepthLimitExceeded = logEntry . WarnDepthLimitExceeded
