{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Internal.InternalBytes (
    InternalBytes (..),
) where

import Data.ByteString (
    ByteString,
 )
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Attribute.Pattern.Defined
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Pattern.Function
import Kore.Attribute.Pattern.Functional
import Kore.Attribute.Synthetic
import qualified Kore.Builtin.Encoding as Encoding
import Kore.Debug
import Kore.Syntax
import Kore.Unparser
import Prelude.Kore

data InternalBytes = InternalBytes
    { internalBytesSort :: !Sort
    , internalBytesValue :: !ByteString
    }
    deriving stock (Eq, Ord, Show)
    deriving stock (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

instance Unparse InternalBytes where
    unparse internalBytes@(InternalBytes _ _) =
        "\\dv"
            <> parameters [internalBytesSort]
            <> arguments [StringLiteral (Encoding.decode8Bit internalBytesValue)]
      where
        InternalBytes{internalBytesSort, internalBytesValue} = internalBytes

    unparse2 internalBytes@(InternalBytes _ _) =
        "\\dv2"
            <> parameters2 [internalBytesSort]
            <> arguments2 [StringLiteral (Encoding.decode8Bit internalBytesValue)]
      where
        InternalBytes{internalBytesSort, internalBytesValue} = internalBytes

instance Synthetic Sort (Const InternalBytes) where
    synthetic = internalBytesSort . getConst
    {-# INLINE synthetic #-}

instance Synthetic (FreeVariables variable) (Const InternalBytes) where
    synthetic = const emptyFreeVariables
    {-# INLINE synthetic #-}

instance Synthetic Defined (Const InternalBytes) where
    synthetic = alwaysDefined
    {-# INLINE synthetic #-}

instance Synthetic Function (Const InternalBytes) where
    synthetic = alwaysFunction
    {-# INLINE synthetic #-}

instance Synthetic Functional (Const InternalBytes) where
    synthetic = alwaysFunctional
    {-# INLINE synthetic #-}
