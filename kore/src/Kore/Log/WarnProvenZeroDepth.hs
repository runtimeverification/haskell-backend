{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.WarnProvenZeroDepth
    ( WarnProvenZeroDepth (..)
    , warnIfProvenWithZeroDepth
    ) where

import Prelude.Kore

import Kore.Log.InfoProofDepth
import Log
import Pretty
    ( Pretty
    )
import qualified Pretty

data WarnProvenZeroDepth = WarnProvenZeroDepth
    deriving Show

instance Pretty WarnProvenZeroDepth where
    pretty _ = "claim proven without taking any steps"

instance Entry WarnProvenZeroDepth where
    entrySeverity _ = Warning
    helpDoc _ = "warn when a claim is proven without taking any steps"

warnIfProvenWithZeroDepth :: MonadLog log => ProofDepth -> log ()
warnIfProvenWithZeroDepth (ProofDepth depth) =
    when (depth == 0) $ logEntry WarnProvenZeroDepth
