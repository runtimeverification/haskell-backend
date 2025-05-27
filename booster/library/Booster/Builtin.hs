{- |
Copyright   : (c) Runtime Verification, 2023
License     : BSD-3-Clause

Builtin functions as described in [docs/hooks.md](https://github.com/runtimeverification/haskell-backend/blob/master/docs/hooks.md).
Only selected functions are implemented.

Built-in functions are looked up by their symbol attribute 'hook' from
the definition's symbol map.

The built-in function fails outright when its function is called with
a wrong argument count. When required arguments are unevaluated, the
hook returns 'Nothing'.
-}
module Booster.Builtin (
    hooks,
) where

import Data.ByteString (ByteString)
import Data.Map (Map)
import Data.Map qualified as Map

import Booster.Builtin.BOOL
import Booster.Builtin.Base
import Booster.Builtin.BYTES
import Booster.Builtin.INT
import Booster.Builtin.KEQUAL
import Booster.Builtin.LIST
import Booster.Builtin.MAP

hooks :: Map ByteString BuiltinFunction
hooks =
    Map.unions
        [ builtinsBOOL
        , builtinsINT
        , builtinsMAP
        , builtinsLIST
        , builtinsKEQUAL
        , builtinsBYTES
        ]
