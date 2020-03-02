{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Internal.InternalBytes
    ( InternalBytes (..)
    ) where

import Prelude.Kore

import Control.DeepSeq
    ( NFData (..)
    )
import Data.ByteString
    ( ByteString
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import qualified Kore.Builtin.Encoding as Encoding
import Kore.Debug
import Kore.Syntax
import Kore.Unparser

data InternalBytes =
    InternalBytes
        { bytesSort          :: !Sort
        , bytesValue         :: !ByteString
        }
    deriving (Eq, GHC.Generic, Ord, Show)

instance Hashable InternalBytes

instance NFData InternalBytes

instance SOP.Generic InternalBytes

instance SOP.HasDatatypeInfo InternalBytes

instance Debug InternalBytes

instance Diff InternalBytes

instance Unparse InternalBytes where
    unparse internalBytes@(InternalBytes _ _) =
        "\\dv"
        <> parameters [bytesSort]
        <> arguments [StringLiteral (Encoding.toBase16 bytesValue)]
      where
        InternalBytes { bytesSort, bytesValue } = internalBytes

    unparse2 internalBytes@(InternalBytes _ _) =
        "\\dv2"
        <> parameters2 [bytesSort]
        <> arguments2 [StringLiteral (Encoding.toBase16 bytesValue)]
      where
        InternalBytes { bytesSort, bytesValue } = internalBytes

instance Synthetic Sort (Const InternalBytes) where
    synthetic = bytesSort . getConst
    {-# INLINE synthetic #-}

instance
    Ord variable =>
    Synthetic (FreeVariables variable) (Const InternalBytes)
  where
    synthetic = const mempty
    {-# INLINE synthetic #-}
