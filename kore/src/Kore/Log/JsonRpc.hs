{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Log.JsonRpc (
    LogJsonRpcServer (..),
) where

import Control.Monad.Logger (
    Loc,
    LogLevel (..),
    LogSource,
    LogStr,
    defaultLogStr,
    fromLogStr,
 )
import Data.Text.Encoding qualified as Text
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
 )

data LogJsonRpcServer = LogJsonRpcServer
    { loc :: Loc
    , src :: LogSource
    , level :: LogLevel
    , msg :: LogStr
    }
    deriving stock (Show)

instance Pretty LogJsonRpcServer where
    pretty LogJsonRpcServer{loc, src, level, msg} = pretty $ Text.decodeUtf8 $ fromLogStr $ defaultLogStr loc src level msg

instance Entry LogJsonRpcServer where
    entrySeverity LogJsonRpcServer{level} = case level of
        LevelDebug -> Debug
        LevelInfo -> Info
        LevelWarn -> Warning
        LevelError -> Error
        _ -> Debug
    helpDoc _ = "log JSON RPC Server messages"
    oneLineDoc LogJsonRpcServer{msg} = pretty $ Text.decodeUtf8 $ fromLogStr msg
