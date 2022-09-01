{-# LANGUAGE BlockArguments #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Data.InternedText (
    -- * Interned text
    InternedText,
    internedText,
    internText,

    -- * Cache
    InternedTextCache (..),
    globalInternedTextCache,
) where

import Data.HashMap.Strict as HashMap
import Data.IORef
import Data.Text (
    Text,
 )
import GHC.Generics (Generic)
import GHC.Generics qualified as GHC
import Generics.SOP qualified as SOP
import Kore.Debug
import Prelude.Kore
import System.IO.Unsafe (unsafePerformIO)

data InternedTextCache = InternedTextCache
    { counter :: {-# UNPACK #-} !Word
    , internedTexts :: !(HashMap Text InternedText)
    }
    deriving stock (Generic)
    deriving anyclass (NFData)

data InternedText = InternedText
    { internedText :: {-# UNPACK #-} !Text
    , internedId :: {-# UNPACK #-} !Word
    }
    deriving stock (GHC.Generic)
    deriving anyclass (NFData)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Show InternedText where
    showsPrec prec = showsPrec prec . internedText

instance Debug InternedText where
    debugPrec = debugPrec . internedText

instance Diff InternedText where
    diffPrec = diffPrec `on` internedText

instance Eq InternedText where
    a == b = internedId a == internedId b
    {-# INLINE (==) #-}

instance Hashable InternedText where
    hashWithSalt salt = hashWithSalt salt . internedId
    {-# INLINE hashWithSalt #-}
    hash = hash . internedId
    {-# INLINE hash #-}

instance Ord InternedText where
    a `compare` b
        -- Quickly check if their interned IDs are equal.
        | internedId a == internedId b = EQ
        -- If they're not, fallback to using lexical order by comparing the strings' actual contents.
        | otherwise = internedText a `compare` internedText b
    {-# INLINE compare #-}

globalInternedTextCache :: IORef InternedTextCache
globalInternedTextCache = unsafePerformIO $ newIORef $ InternedTextCache 0 HashMap.empty
{-# NOINLINE globalInternedTextCache #-}

internText :: Text -> InternedText
internText text =
    unsafePerformIO do
        atomicModifyIORef' globalInternedTextCache \InternedTextCache{counter, internedTexts} ->
            let ((internedText, newCounter), newInternedTexts) =
                    HashMap.alterF
                        \case
                            -- If this text is already interned, reuse it.
                            existing@(Just interned) -> ((interned, counter), existing)
                            -- Otherwise, create a new ID for it and intern it.
                            Nothing ->
                                let newIden = counter
                                    newInterned = InternedText text newIden
                                 in ((newInterned, counter + 1), Just newInterned)
                        text
                        internedTexts
             in (InternedTextCache newCounter newInternedTexts, internedText)
{-# INLINE internText #-}
