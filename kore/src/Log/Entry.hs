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
    , someEntry
    , entryTypeText
    ) where

import Colog
    ( Severity (..)
    )
import qualified Control.Lens as Lens
import Control.Lens.Prism
    ( Prism
    )
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
import Prelude hiding
    ( log
    )
import qualified Type.Reflection as Reflection

class (Pretty entry, Typeable entry) => Entry entry where
    toEntry :: entry -> SomeEntry
    toEntry = SomeEntry

    fromEntry :: SomeEntry -> Maybe entry
    fromEntry (SomeEntry entry) = Data.Typeable.cast entry

    entrySeverity :: entry -> Severity

data SomeEntry where
    SomeEntry :: Entry entry => entry -> SomeEntry

instance Entry SomeEntry where
    toEntry = id
    fromEntry = Just
    entrySeverity (SomeEntry entry) = entrySeverity entry

instance Pretty SomeEntry where
    pretty (SomeEntry entry) = Pretty.pretty entry

someEntry :: (Entry e1, Entry e2) => Prism SomeEntry SomeEntry e1 e2
someEntry = Lens.prism' toEntry fromEntry

entryTypeText :: SomeEntry -> Text
entryTypeText (SomeEntry entry) =
    Text.pack . show . Reflection.typeOf $ entry

prettySeverity :: Severity -> Pretty.Doc ann
prettySeverity = Pretty.pretty . show
