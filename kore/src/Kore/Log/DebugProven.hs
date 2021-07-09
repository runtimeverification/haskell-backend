{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Log.DebugProven (
    DebugProven (..),
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

newtype DebugProven = DebugProven {claim :: SomeClaim}
    deriving stock (Show)

instance Pretty DebugProven where
    pretty DebugProven{claim} =
        Pretty.vsep ["Proved claim:", Pretty.indent 4 (pretty claim)]

instance Entry DebugProven where
    entrySeverity _ = Debug
    helpDoc _ = "log proven claims"
