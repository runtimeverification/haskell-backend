{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Internal.InternalBytes
    ( InternalBytes (..)
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

-- TODO(Bytes): This should be String2Bytes(\dv{StringSort}(string))
instance Unparse InternalBytes where
    unparse InternalBytes { bytesSort, bytesValue, string2BytesSymbol } =
        "\\dv"
        <> parameters [bytesSort]
        <> Pretty.parens
            ( unparse
                Application
                    { applicationSymbolOrAlias =
                        toSymbolOrAlias string2BytesSymbol
                    , applicationChildren =
                        [ DomainValue
                            { domainValueSort =
                                head $ symbolParams string2BytesSymbol
                            , domainValueChild =
                                StringLiteral $ E.decode8Bit bytesValue
                            }
                        ]
                    }
            )

    unparse2 InternalBytes { bytesSort, bytesValue, string2BytesSymbol } =
        "\\dv2"
        <> parameters2 [bytesSort]
        <> arguments2
            [ Application
                { applicationSymbolOrAlias =
                    toSymbolOrAlias string2BytesSymbol
                , applicationChildren =
                    [ DomainValue
                        { domainValueSort =
                            head $ symbolParams string2BytesSymbol
                        , domainValueChild =
                            StringLiteral $ E.decode8Bit bytesValue
                        }
                    ]
                }
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
