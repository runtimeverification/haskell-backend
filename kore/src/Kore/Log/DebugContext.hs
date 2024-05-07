{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Log.DebugContext (
    DebugContext (..),
) where

import Data.Text qualified as Text
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
 )

newtype DebugContext = DebugContext {msg :: Text.Text}
    deriving stock (Show)

instance Pretty DebugContext where
    pretty DebugContext{msg} = pretty msg

instance Entry DebugContext where
    entrySeverity DebugContext{} = Debug
    helpDoc _ = "Plain text debug message to signify an action's context"
    oneLineDoc DebugContext{msg} = pretty msg
    oneLineContextDoc DebugContext{msg} = [pretty msg]
