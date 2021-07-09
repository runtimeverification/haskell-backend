{-# LANGUAGE NoStrict #-}
{-# LANGUAGE NoStrictData #-}

{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Log.Entry (
    -- * Severity
    Severity (..),
    prettySeverity,

    -- * Entry
    Entry (..),
    SomeEntry (..),
    ActualEntry (..),
    someEntry,
    entryTypeText,
) where

import Colog (
    Severity (..),
 )
import Control.Exception (
    Exception (..),
 )
import qualified Control.Lens as Lens
import Control.Lens.Prism (
    Prism,
 )
import Data.Proxy (
    Proxy (..),
 )
import Data.Text (
    Text,
 )
import qualified Data.Text as Text
import qualified Data.Typeable (
    cast,
 )
import Prelude.Kore
import Pretty (
    Pretty,
 )
import qualified Pretty
import qualified Type.Reflection as Reflection

class (Show entry, Typeable entry) => Entry entry where
    toEntry :: entry -> SomeEntry
    toEntry = SomeEntry

    fromEntry :: SomeEntry -> Maybe entry
    fromEntry (SomeEntry entry) = Data.Typeable.cast entry

    entrySeverity :: entry -> Severity

    longDoc :: entry -> Pretty.Doc ann
    default longDoc :: Pretty entry => entry -> Pretty.Doc ann
    longDoc = Pretty.pretty

    oneLineDoc :: entry -> Maybe (Pretty.Doc ann)
    oneLineDoc = const $ Just "One line logging not implemented for this entry"

    contextDoc :: entry -> Maybe (Pretty.Doc ann)
    contextDoc = const Nothing

    helpDoc :: Proxy entry -> Pretty.Doc ann
    helpDoc _ = Pretty.emptyDoc

data SomeEntry where
    SomeEntry :: Entry entry => entry -> SomeEntry

instance Show SomeEntry where
    show (SomeEntry entry) = show entry

instance Exception SomeEntry where
    displayException = show . longDoc

instance Entry SomeEntry where
    toEntry = id
    fromEntry = Just
    entrySeverity (SomeEntry entry) = entrySeverity entry
    longDoc (SomeEntry entry) = longDoc entry
    oneLineDoc (SomeEntry entry) = oneLineDoc entry
    contextDoc (SomeEntry entry) = contextDoc entry

someEntry :: (Entry e1, Entry e2) => Prism SomeEntry SomeEntry e1 e2
someEntry = Lens.prism' toEntry fromEntry

entryTypeText :: SomeEntry -> Text
entryTypeText (SomeEntry entry) =
    Text.pack . show . Reflection.typeOf $ entry

data ActualEntry = ActualEntry
    { actualEntry :: !SomeEntry
    , entryContext :: ![SomeEntry]
    }

instance From ActualEntry SomeEntry where
    from ActualEntry{actualEntry} = actualEntry

instance From SomeEntry ActualEntry where
    from actualEntry = ActualEntry{actualEntry, entryContext = mempty}

prettySeverity :: Severity -> Pretty.Doc ann
prettySeverity = Pretty.pretty . show
