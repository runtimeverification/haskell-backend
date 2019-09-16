{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Builtin.Bytes.Bytes
    ( Bytes (..)

    , Internal (..)
    , lengthInternal
    , getInternal
    , replicateInternal

    , String2Bytes (..)
    , fromChar
    , string2bytesInternal

    , Update (..)
    , updateInternal

    , Substr (..)
    , takeInternal
    , dropInternal
    , substrInternal

    , ReplaceAt (..)
    , replaceAtInternal

    , PadRight (..)
    , padRightInternal

    , PadLeft (..)
    , padLeftInternal

    , Reverse (..)
    , reverseInternal

    , Concat (..)
    , concatInternal
    ) where

import qualified Control.Monad as Monad
import Data.ByteString
    ( ByteString
    )
import qualified Data.ByteString as ByteString
import qualified Data.Char as Char
import Data.Sequence
    ( Seq
    )
import qualified Data.Sequence as Seq
import qualified Data.Text as Text
import Data.Word
    ( Word8
    )
import qualified Generics.SOP as SOP
import qualified GHC.Generics as GHC

import Kore.Debug
import Kore.Internal.ApplicationSorts
import Kore.Internal.Symbol
    ( Symbol (..)
    )
import Kore.Syntax.Application
import Kore.Syntax.DomainValue
import Kore.Syntax.StringLiteral
import Kore.Unparser

{- | @Bytes@ represents the builtin sort @BYTES.Bytes@.
 -}
data Bytes term
    = BytesInternal     !Internal
    | BytesString2Bytes !(String2Bytes term)
    | BytesUpdate       !(Update term)
    | BytesSubstr       !(Substr term)
    | BytesReplaceAt    !(ReplaceAt term)
    | BytesPadRight     !(PadRight term)
    | BytesPadLeft      !(PadLeft term)
    | BytesReverse      !(Reverse term)
    | BytesConcat       !(Concat term)
    | BytesTerm         !term
    deriving (Functor, GHC.Generic)

instance SOP.Generic (Bytes term)

instance SOP.HasDatatypeInfo (Bytes term)

instance Debug term => Debug (Bytes term)

instance Unparse term => Unparse (Bytes term) where
    unparse = unparseGeneric
    unparse2 = unparse2Generic

{- | The internal representation of a concrete byte array.
 -}
data Internal =
    Internal
        { symbol :: !Symbol
        -- ^ The 'Symbol' hooked to @BYTES.string2bytes@, for 'Unparse'.
        , bytes :: !ByteString
        -- ^ The concrete array of bytes.
        }
    deriving (Eq, GHC.Generic, Show)

instance Semigroup Internal where
    (<>) Internal { symbol, bytes = bytes1 } Internal { bytes = bytes2 } =
        Internal { symbol, bytes = bytes1 <> bytes2 }

instance SOP.Generic Internal

instance SOP.HasDatatypeInfo Internal

instance Debug Internal

instance Unparse Internal where
    unparseVia go Internal { symbol, bytes } =
        go Application
            { applicationSymbolOrAlias = symbol
            , applicationChildren =
                [ DomainValue
                    { domainValueSort
                    , domainValueChild = StringLiteral literal
                    }
                ]
            }
      where
        Symbol { symbolSorts } = symbol
        [domainValueSort] = applicationSortsOperands symbolSorts
        literal =
            Text.pack $ map (Char.chr . fromEnum) $ ByteString.unpack bytes

{- | The length of a concrete byte array.
 -}
lengthInternal :: Internal -> Int
lengthInternal Internal { bytes } = ByteString.length bytes

{- | Get the byte at the index.
 -}
getInternal :: Internal -> Int -> Maybe Word8
getInternal Internal { bytes } ix
  | 0 <= ix, ix < ByteString.length bytes = Just (ByteString.index bytes ix)
  | otherwise                             = Nothing

{- | A byte array with the same byte at every position.
 -}
replicateInternal :: Symbol -> Int -> Word8 -> Maybe Internal
replicateInternal symbol len' byte' = do
    Monad.guard (0 <= len')
    pure Internal { symbol, bytes = ByteString.replicate len' byte' }

{- | @String2Bytes@ represents the builtin symbol @BYTES.string2bytes@.
 -}
data String2Bytes string =
    String2Bytes
        { symbol :: !Symbol
        -- ^ The 'Symbol' hooked to @BYTES.string2bytes@, for 'Unparse'.
        , string :: !string
        -- ^ The @STRING.String@ pattern representing the @BYTES.Bytes@.
        }
    deriving (Functor, GHC.Generic)

instance SOP.Generic (String2Bytes string)

instance SOP.HasDatatypeInfo (String2Bytes string)

instance Debug string => Debug (String2Bytes string)

instance Unparse string => Unparse (String2Bytes string) where
    unparseVia go String2Bytes { symbol, string } =
        go (Application symbol [string])

{- | Decode a 'Char' to a byte.
 -}
fromChar :: Char -> Maybe Word8
fromChar c
  | 0 <= o, o < 0x100 = Just (toEnum o)
  | otherwise = Nothing
  where
    o = Char.ord c

{- | Internal implementation of @BYTES.string2bytes@.
 -}
string2bytesInternal :: Symbol -> String -> Maybe Internal
string2bytesInternal symbol string' = do
    bytes <- ByteString.pack <$> traverse fromChar string'
    pure Internal { symbol, bytes }

{- | @Update@ represents the builtin symbol @BYTES.update@.
 -}
data Update term =
    Update
        { symbol :: !Symbol
        -- ^ The 'Symbol' hooked to @BYTES.update@, for 'Unparse'.
        , bytes :: !(Bytes term)
        -- ^ The original byte array, to be updated.
        , offset :: !term
        -- ^ The @INT.Int@ position of the new @byte@.
        , byte :: !term
        -- ^ The @INT.Int@ of the new byte to place at @offset@.
        }
    deriving (Functor, GHC.Generic)

instance SOP.Generic (Update term)

instance SOP.HasDatatypeInfo (Update term)

instance Debug term => Debug (Update term)

instance Unparse term => Unparse (Update term) where
    unparseVia go Update { symbol, bytes, offset, byte } =
        go Application
            { applicationSymbolOrAlias = symbol
            , applicationChildren =
                [SomeUnparse bytes, SomeUnparse offset, SomeUnparse byte]
            }

{- | Internal implementation of @BYTES.update@.
 -}
updateInternal :: Internal -> Int -> Word8 -> Maybe Internal
updateInternal Internal { symbol, bytes } offset' byte' = do
    Monad.guard (0 <= offset')
    Monad.guard (offset' < ByteString.length bytes)
    let (before, ByteString.tail -> after) = ByteString.splitAt offset' bytes
    let bytes' = before <> ByteString.cons byte' after
    pure Internal { symbol, bytes = bytes' }

{- | @Substr@ represents the builtin symbol @BYTES.substr@.
 -}
data Substr term =
    Substr
        { symbol :: !Symbol
        -- ^ The 'Symbol' hooked to @BYTES.substr@, for 'Unparse'.
        , bytes  :: !(Bytes term)
        -- ^ The original byte array.
        , offset :: !term
        -- ^ The @INT.Int@ offset (in the original byte array) of the result.
        , len    :: !term
        -- ^ The @INT.Int@ length of the result.
        }
    deriving (Functor, GHC.Generic)

instance SOP.Generic (Substr term)

instance SOP.HasDatatypeInfo (Substr term)

instance Debug term => Debug (Substr term)

instance Unparse term => Unparse (Substr term) where
    unparseVia go Substr { symbol, bytes, offset, len } =
        go Application
            { applicationSymbolOrAlias = symbol
            , applicationChildren =
                [SomeUnparse bytes, SomeUnparse offset, SomeUnparse len]
            }

{- | Internal implementation of @BYTES.substr@.
 -}
substrInternal :: Internal -> Int -> Int -> Maybe Internal
substrInternal Internal { symbol, bytes } offset' len' = do
    Monad.guard (0 <= offset')
    Monad.guard (0 <= len')
    Monad.guard (offset' + len' <= ByteString.length bytes)
    let bytes' = ByteString.take len' . ByteString.drop offset' $ bytes
    pure Internal { symbol, bytes = bytes' }

{- | @takeInternal internal n@ is the first @n@ bytes of @internal@.
 -}
takeInternal :: Internal -> Int -> Maybe Internal
takeInternal internal len' = substrInternal internal 0 len'

{- | @dropInternal internal n@ is all but the first @n@ bytes of @internal@.
 -}
dropInternal :: Internal -> Int -> Maybe Internal
dropInternal internal offset' = do
    let len' = lengthInternal internal
    substrInternal internal offset' (len' - offset')

{- | @ReplaceAt@ represents the builtin symbol @BYTES.replaceAt@.
 -}
data ReplaceAt term =
    ReplaceAt
        { symbol :: !Symbol
        -- ^ The 'Symbol' hooked to @BYTES.replaceAt@, for 'Unparse'.
        , original  :: !(Bytes term)
        -- ^ The original byte array.
        , offset :: !term
        -- ^ The @INT.Int@ offset where replacement begins.
        , replace :: !(Bytes term)
        -- ^ The replacement byte array.
        }
    deriving (Functor, GHC.Generic)

instance SOP.Generic (ReplaceAt term)

instance SOP.HasDatatypeInfo (ReplaceAt term)

instance Debug term => Debug (ReplaceAt term)

instance Unparse term => Unparse (ReplaceAt term) where
    unparseVia go ReplaceAt { symbol, original, offset, replace } =
        go Application
            { applicationSymbolOrAlias = symbol
            , applicationChildren =
                [SomeUnparse original, SomeUnparse offset, SomeUnparse replace]
            }

{- | Internal implementation of @BYTES.replaceAt@.
 -}
replaceAtInternal :: Internal -> Int -> Internal -> Maybe Internal
replaceAtInternal original offset' replace = do
    let lenOriginal = lengthInternal original
        lenReplace = lengthInternal replace
    Monad.guard (offset' + lenReplace <= lenOriginal)
    before <- takeInternal original offset'
    after <- dropInternal original (offset' + lenReplace)
    pure (before <> replace <> after)

{- | @PadRight@ represents the builtin symbol @BYTES.padRight@.
 -}
data PadRight term =
    PadRight
        { symbol :: !Symbol
        -- ^ The 'Symbol' hooked to @BYTES.padRight@, for 'Unparse'.
        , bytes  :: !(Bytes term)
        -- ^ The original byte array.
        , len    :: !term
        -- ^ The @INT.Int@ length of padding.
        , byte   :: !term
        -- ^ The @INT.Int@ byte to pad with.
        }
    deriving (Functor, GHC.Generic)

instance SOP.Generic (PadRight term)

instance SOP.HasDatatypeInfo (PadRight term)

instance Debug term => Debug (PadRight term)

instance Unparse term => Unparse (PadRight term) where
    unparseVia go PadRight { symbol, bytes, len, byte } =
        go Application
            { applicationSymbolOrAlias = symbol
            , applicationChildren =
                [SomeUnparse bytes, SomeUnparse len, SomeUnparse byte]
            }

{- | Internal implementation of @BYTES.padRight@.
 -}
padRightInternal :: Internal -> Int -> Word8 -> Maybe Internal
padRightInternal internal@Internal { symbol } len' byte' = do
    padding <- replicateInternal symbol len' byte'
    pure (internal <> padding)

{- | @PadLeft@ represents the builtin symbol @BYTES.padLeft@.
 -}
data PadLeft term =
    PadLeft
        { symbol :: !Symbol
        -- ^ The 'Symbol' hooked to @BYTES.padLeft@, for 'Unparse'.
        , bytes  :: !(Bytes term)
        -- ^ The original byte array.
        , len    :: !term
        -- ^ The @INT.Int@ length of padding.
        , byte  :: !term
        -- ^ The @INT.Int@ byte to pad with.
        }
    deriving (Functor, GHC.Generic)

instance SOP.Generic (PadLeft term)

instance SOP.HasDatatypeInfo (PadLeft term)

instance Debug term => Debug (PadLeft term)

instance Unparse term => Unparse (PadLeft term) where
    unparseVia go PadLeft { symbol, bytes, len, byte } =
        go Application
            { applicationSymbolOrAlias = symbol
            , applicationChildren =
                [SomeUnparse bytes, SomeUnparse len, SomeUnparse byte]
            }

{- | Internal implementation of @BYTES.padLeft@.
 -}
padLeftInternal :: Internal -> Int -> Word8 -> Maybe Internal
padLeftInternal internal@Internal { symbol } len' byte' = do
    padding <- replicateInternal symbol len' byte'
    pure (padding <> internal)

{- | @Reverse@ represents the builtin symbol @BYTES.reverse@.
 -}
data Reverse term =
    Reverse
        { symbol :: !Symbol
        -- ^ The 'Symbol' hooked to @BYTES.reverse@, for 'Unparse'.
        , bytes :: !(Bytes term)
        -- ^ The original byte array.
        }
    deriving (Functor, GHC.Generic)

instance SOP.Generic (Reverse term)

instance SOP.HasDatatypeInfo (Reverse term)

instance Debug term => Debug (Reverse term)

instance Unparse term => Unparse (Reverse term) where
    unparseVia go Reverse { symbol, bytes } =
        go Application
            { applicationSymbolOrAlias = symbol
            , applicationChildren = [SomeUnparse bytes]
            }

{- | Internal implementation of @BYTES.reverse@.
 -}
reverseInternal :: Internal -> Internal
reverseInternal Internal { symbol, bytes } =
    Internal { symbol, bytes = ByteString.reverse bytes }

{- | @Concat@ represents the builtin symbol @BYTES.concat@.

@BYTES.concat@ is the associative concatenation operator on byte arrays.

 -}
data Concat term =
    Concat
        { symbol :: !Symbol
        -- ^ The 'Symbol' hooked to @BYTES.concat@, for 'Unparse'.
        , concat1 :: !(Bytes term)
        -- ^ The first byte array in the concatenation.
        , concatI :: !(Seq (Bytes term))
        -- ^ The interior of the concatenation.
        , concatN :: !(Bytes term)
        -- ^ The last byte array in the concatenation.
        }
    deriving (Functor, GHC.Generic)

instance SOP.Generic (Concat term)

instance SOP.HasDatatypeInfo (Concat term)

instance Debug term => Debug (Concat term)

instance Unparse term => Unparse (Concat term) where
    unparseVia go Concat { symbol, concat1, concatI, concatN } =
        go Application
            { applicationSymbolOrAlias = symbol
            , applicationChildren =
                [SomeUnparse concat1, concat']
            }
      where
        concat' =
            case concatI of
                Seq.Empty ->
                    SomeUnparse concatN
                concat1' Seq.:<| concatI' ->
                    SomeUnparse Concat
                        { symbol
                        , concat1 = concat1'
                        , concatI = concatI'
                        , concatN
                        }

{- | Internal implementation of @BYTES.concat@.
 -}
concatInternal :: Internal -> Seq Internal -> Internal -> Internal
concatInternal concat1' concatI' concatN' =
    concat1' <> foldr (<>) concatN' concatI'
