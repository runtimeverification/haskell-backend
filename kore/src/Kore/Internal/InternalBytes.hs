{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Internal.InternalBytes
    ( InternalBytes (..)
    , toApplication
    ) where

import Control.DeepSeq
    ( NFData (..)
    )
import qualified Data.ByteString as BS
import Data.Hashable
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Attribute.Pattern.FreeVariables
import Kore.Attribute.Synthetic
import qualified Kore.Builtin.Encoding as E
import Kore.Debug
import qualified Kore.Domain.Builtin as Domain
import Kore.Internal.Symbol
import Kore.Syntax
import Kore.Unparser

data InternalBytes =
    InternalBytes
        { bytesSort          :: !Sort
        , bytesValue         :: !BS.ByteString
        , string2BytesSymbol :: !Symbol
        }
    deriving (Eq, GHC.Generic, Ord, Show)

instance Hashable InternalBytes

instance NFData InternalBytes

instance SOP.Generic InternalBytes

instance SOP.HasDatatypeInfo InternalBytes

instance Debug InternalBytes

instance Diff InternalBytes

instance Unparse InternalBytes where
    unparse internalBytes =
        "\\dv"
        <> parameters [bytesSort internalBytes]
        <> Pretty.parens
            (unparse $ toApplication internalBytes)

    unparse2 internalBytes =
        "\\dv2"
        <> parameters2 [bytesSort internalBytes]
        <> arguments2
            [ toApplication internalBytes
            ]

instance Synthetic Sort (Const InternalBytes) where
    synthetic = bytesSort . getConst
    {-# INLINE synthetic #-}

instance
    Ord variable =>
    Synthetic (FreeVariables variable) (Const InternalBytes)
  where
    synthetic = const mempty
    {-# INLINE synthetic #-}

toApplication :: InternalBytes -> Application SymbolOrAlias Domain.InternalString
toApplication InternalBytes { bytesValue, string2BytesSymbol } =
    Application
        { applicationSymbolOrAlias =
            toSymbolOrAlias string2BytesSymbol
        , applicationChildren =
            [ Domain.InternalString
                { Domain.internalStringSort =
                    head $ symbolParams string2BytesSymbol
                , Domain.internalStringValue =
                    E.decode8Bit bytesValue
                }
            ]
        }
