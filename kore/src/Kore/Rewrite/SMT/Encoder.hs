{- |
Module      : Kore.Rewrite.SMT.Encoder
Description : Encodes names for the SMT solver.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
-}
module Kore.Rewrite.SMT.Encoder (encodeName) where

import Data.Text (
    Text,
 )
import Prelude.Kore

{- | Encodes a name in order to remove special characters and to
prevent conflicts with SMT builtins.
-}
encodeName :: Text -> Text
encodeName name =
    "|HB_" <> name <> "|"

-- `HB` = Haskell backend
-- `|` is used to allow special characters like `'`
