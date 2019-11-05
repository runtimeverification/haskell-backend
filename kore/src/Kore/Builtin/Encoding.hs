{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
 -}

module Kore.Builtin.Encoding
    ( encode8Bit
    , decode8Bit
    ) where

import Control.Category
    ( (>>>)
    )
import Data.ByteString
    ( ByteString
    )
import qualified Data.ByteString as ByteString
import Data.Char as Char
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import Data.Word
    ( Word8
    )

{- | Encode text using an 8-bit encoding.

Each 'Char' in the text is interpreted as a 'Data.Word.Word8'. It is an error if
any character falls outside that representable range.

 -}
encode8Bit :: Text -> ByteString
encode8Bit =
    Text.unpack
    >>> map (Char.ord >>> encodeByte)
    >>> ByteString.pack
  where
    encodeByte :: Int -> Word8
    encodeByte int
      | int < 0x00 = failed "expected positive value"
      | int > 0xFF = failed "expected 8-bit value"
      | otherwise = fromIntegral int
      where
        failed message =
            (error . unwords)
                [ "encode8Bit:"
                , message ++ ","
                , "found:"
                , show int
                ]

decode8Bit :: ByteString -> Text
decode8Bit =
    ByteString.unpack
    >>> map (Char.chr . fromIntegral)
    >>> Text.pack
