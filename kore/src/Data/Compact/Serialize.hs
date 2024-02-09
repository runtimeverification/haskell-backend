{- | Drop-in replacement for Data.Compact.Serialize of the `compact`
  library (which appears unmaintained at the time of writing).

  Original: Copyright (c) 2017, Edward Z. Yang

  This adaptation: Copyright (c) 2023, Runtime Verification Inc.

All rights reserved.

Redistribution and use in source and binary forms, with or without
modification, are permitted provided that the following conditions are met:

    * Redistributions of source code must retain the above copyright
      notice, this list of conditions and the following disclaimer.

    * Redistributions in binary form must reproduce the above
      copyright notice, this list of conditions and the following
      disclaimer in the documentation and/or other materials provided
      with the distribution.

    * Neither the name of Edward Z. Yang nor the names of other
      contributors may be used to endorse or promote products derived
      from this software without specific prior written permission.

THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
"AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
OWNER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
(INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
-}
module Data.Compact.Serialize (
    writeCompact,
    unsafeReadCompact,
    hPutCompact,
    hUnsafeGetCompact,
    hHasCompactMarker,
) where

import Control.Monad
import Data.Binary qualified as B
import Data.ByteString.Lazy qualified as BSL
import Data.Monoid
import Data.Word
import Foreign.Marshal.Alloc
import Foreign.Ptr
import Foreign.Storable
import GHC.Compact hiding (compact)
import GHC.Compact.Serialized
import GHC.Fingerprint qualified as Fingerprint
import System.Environment (getExecutablePath)
import System.IO
import System.IO.Unsafe (unsafePerformIO)
import Type.Reflection

import Prelude

{- | Write a compact region to a file.  The resulting file can
be read back into memory using 'unsafeReadCompact'.
-}
writeCompact :: Typeable a => FilePath -> Compact a -> IO ()
writeCompact fname compact =
    withFile fname WriteMode $ \h -> hPutCompact h compact

{- | Write a compact region to a 'Handle'.  The compact region
can be read out of the handle by using 'hUnsafeGetCompact'.
-}
hPutCompact :: Typeable a => Handle -> Compact a -> IO ()
hPutCompact hdl compact =
    withSerializedCompact compact $ \scompact -> do
        -- write a format marker first
        BSL.hPut hdl compactMarker
        let bs = B.encode $ CompactFile scompact
        -- By writing out the length of the metadata segment, we
        -- can read out a single word, read out the metadata segment,
        -- and then immediately start blasting further data from
        -- the handle into the memory region where the compact
        -- is going to go.  Otherwise, we have to indirect through
        -- a lazy bytestring which has a cost.
        hPutStorable hdl (fromIntegral (BSL.length bs) :: Int)
        BSL.hPut hdl bs
        let putBlock (ptr, len) = hPutBuf hdl ptr (fromIntegral len)
        mapM_ putBlock (serializedCompactBlockList scompact)

{- | Read out a compact region that was serialized to a file.
See 'hUnsafeGetCompact' for safety considerations when using this function.
-}
unsafeReadCompact :: Typeable a => FilePath -> IO (Either String (Compact a))
unsafeReadCompact fname =
    withFile fname ReadMode $ \hdl -> hUnsafeGetCompact hdl

{- | Read out a compact region from a handle.

Compact regions written to handles this way are subject to some
restrictions:

 * Our binary representation contains direct pointers to the info
   tables of objects in the region.  This means that the info tables
   of the receiving process must be laid out in exactly the same
   way as from the original process; in practice, this means using
   static linking, using the exact same binary and turning off ASLR.  This
   API only does a very basic check and will probably segfault if you
   get it wrong.  DO NOT run this on untrusted input.

 * You must read out the value at the correct type.  We will
   check this for you and raise an error if the types do not match
   (this is what the 'Typeable' constraint is for).
-}
hUnsafeGetCompact ::
    forall a.
    Typeable a =>
    Handle ->
    IO (Either String (Compact a))
hUnsafeGetCompact hdl = do
    marker <- BSL.hGet hdl (fromIntegral $ BSL.length compactMarker)
    if (marker /= compactMarker)
        then
            return . Left $
                "Unexpected format marker: expected "
                    <> show compactMarker
                    <> ", found "
                    <> show marker
        else do
            l <- hGetStorable hdl
            mbs <- BSL.hGet hdl (l :: Int)
            case B.decodeOrFail @(CompactFile a) mbs of
                Left (_, _, err) -> return $ Left err
                Right (rest, _, CompactFile scompact)
                    | not (BSL.null rest) ->
                        return . Left $
                            "Had " ++ show (BSL.length rest) ++ " bytes of leftover metadata"
                    | otherwise -> do
                        res <- importCompact scompact $ \ptr len ->
                            void $ hGetBuf hdl ptr (fromIntegral len)
                        case res of
                            Nothing -> return $ Left "Failed to import compact"
                            Just compact -> return $ Right compact

{- | Check if a handle points to a compact marker (start of serialized compact data)
and rewind the handle to its previous position
-}
hHasCompactMarker :: Handle -> IO Bool
hHasCompactMarker handle = do
    marker <- BSL.hGet handle offset
    hSeek handle RelativeSeek (negate offset)
    pure $ compactMarker == marker
    where
        offset :: Integral a => a
        offset = fromIntegral $ BSL.length compactMarker

----------------------------------------

newtype CompactFile a = CompactFile (SerializedCompact a)

-- NB: This instance cannot be put on SerializedCompact as
-- ghc-compact does not have a binary dependency
instance Typeable a => B.Binary (CompactFile a) where
    get = do
        magic <- B.get
        when (magic /= magicNumber) $
            fail
                "Data.Compact.Serialized:\
                \ Executable mismatch, data was serialized by a different executable."
        SomeTypeRep tyrep <- B.get
        case tyrep `eqTypeRep` typeRep @a of
            Just HRefl -> CompactFile <$> getSerializedCompact
            Nothing ->
                fail $
                    "Data.Compact.Serialized: expected "
                        ++ show (typeRep @a)
                        ++ " but got "
                        ++ show tyrep
    put (CompactFile a) = B.put magicNumber >> B.put (typeRep @a) >> putSerializedCompact a

compactMarker :: BSL.ByteString
compactMarker = "COMPACT"

-- Integrity check for stored data: ensure the memory layout is the
-- same by requiring the _executable_binary_ to be the same.
{-# NOINLINE magicNumber #-}
magicNumber :: Fingerprint.Fingerprint
magicNumber = unsafePerformIO $ getExecutablePath >>= Fingerprint.getFileHash

-- magicNumber = 0x7c155e7a53f094f2

putPtr :: Ptr a -> B.Put
putPtr = B.put @Word64 . fromIntegral . ptrToWordPtr

getPtr :: B.Get (Ptr a)
getPtr = wordPtrToPtr . fromIntegral <$> B.get @Word64

getList :: B.Get a -> B.Get [a]
getList getElem = do
    n <- B.get @Int
    replicateM n getElem

putList :: (a -> B.Put) -> [a] -> B.Put
putList putElem xs = do
    B.put @Int (length xs)
    mapM_ putElem xs

getSerializedCompact :: B.Get (SerializedCompact a)
getSerializedCompact = SerializedCompact <$> getList getBlock <*> getPtr
    where
        getBlock :: B.Get (Ptr a, Word)
        getBlock = (,) <$> getPtr <*> B.get

putSerializedCompact :: SerializedCompact a -> B.Put
putSerializedCompact (SerializedCompact a b) = putList putBlock a <> putPtr b
    where
        putBlock :: (Ptr a, Word) -> B.Put
        putBlock (ptr, len) = putPtr ptr <> B.put len

hPutStorable :: forall a. Storable a => Handle -> a -> IO ()
hPutStorable h a =
    alloca $ \ptr -> do
        poke ptr a
        hPutBuf h ptr (sizeOf (undefined :: a))

hGetStorable :: forall a. Storable a => Handle -> IO a
hGetStorable h =
    alloca $ \ptr -> do
        void $ hGetBuf h ptr (sizeOf (undefined :: a))
        peek ptr
