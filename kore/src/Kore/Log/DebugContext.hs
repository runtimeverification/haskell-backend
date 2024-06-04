{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Log.DebugContext (
    DebugContext (..),
    inContext,
) where

import Data.Aeson qualified as JSON
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
    oneLineContextDoc DebugContext{msg} = [msg]
    oneLineJson DebugContext{} = JSON.Null
    oneLineContextJson DebugContext{msg} = JSON.String msg

inContext :: MonadLog log => Text.Text -> log a -> log a
inContext = logWhile . DebugContext
