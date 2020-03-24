{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Log.Entry
    (
    -- * Severity
      Severity (..), prettySeverity
    -- * Entry
    , Entry (..)
    , SomeEntry (..)
    , ActualEntry (..)
    , someEntry
    , entryTypeText
    ) where

import Prelude.Kore

import Colog
    ( Severity (..)
    )
import qualified Control.Lens as Lens
import Control.Lens.Prism
    ( Prism
    )
import Data.Sequence
    ( Seq
    )
import qualified Data.Sequence as Seq
import Data.Text
    ( Text
    )
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
    ( Pretty
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
import Data.Typeable
    ( Typeable
    )
import qualified Data.Typeable
    ( cast
    )
import qualified Type.Reflection as Reflection

class Typeable entry => Entry entry where
    toEntry :: entry -> SomeEntry
    toEntry = SomeEntry

    fromEntry :: SomeEntry -> Maybe entry
    fromEntry (SomeEntry entry) = Data.Typeable.cast entry

    entrySeverity :: entry -> Severity

    longDoc :: entry -> Pretty.Doc ann
    default longDoc :: Pretty entry => entry -> Pretty.Doc ann
    longDoc = Pretty.pretty

    shortDoc :: entry -> Maybe (Pretty.Doc ann)
    shortDoc = const Nothing

data SomeEntry where
    SomeEntry :: Entry entry => entry -> SomeEntry

instance Entry SomeEntry where
    toEntry = id
    fromEntry = Just
    entrySeverity (SomeEntry entry) = entrySeverity entry
    longDoc (SomeEntry entry) = longDoc entry
    shortDoc (SomeEntry entry) = shortDoc entry

someEntry :: (Entry e1, Entry e2) => Prism SomeEntry SomeEntry e1 e2
someEntry = Lens.prism' toEntry fromEntry

entryTypeText :: SomeEntry -> Text
entryTypeText (SomeEntry entry) =
    Text.pack . show . Reflection.typeOf $ entry

data ActualEntry =
    ActualEntry
        { actualEntry :: !SomeEntry
        , entryContext :: !(Seq SomeEntry)
        }

instance From ActualEntry SomeEntry where
    from ActualEntry { actualEntry } = actualEntry

instance From SomeEntry ActualEntry where
    from actualEntry =
        ActualEntry { actualEntry, entryContext = Seq.empty }

prettySeverity :: Severity -> Pretty.Doc ann
prettySeverity = Pretty.pretty . show
