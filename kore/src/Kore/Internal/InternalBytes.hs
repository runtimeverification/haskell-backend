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

import Kore.Attribute.Pattern.Defined
import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Pattern.Function
import Kore.Attribute.Pattern.Functional
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
    deriving (Eq, Ord, Show)
    deriving (GHC.Generic)
    deriving anyclass (Hashable, NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)
    deriving anyclass (Debug, Diff)

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
