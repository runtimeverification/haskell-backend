{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Log.Entry
    (
    -- * Severity
      Severity (..)
    -- * Entry
    , Entry (..)
    , SomeEntry (..)
    , someEntry
    , entryTypeText
    ) where

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

-- | Log level used to describe each log message. It is also used to set the
-- minimum level to be outputted.
data Severity
    = Debug
    -- ^ Lowest level used for low-level debugging.
    | Info
    -- ^ Used for various informative messages.
    | Warning
    -- ^ Used for odd/unusual cases which are recoverable.
    | Error
    -- ^ Used for application errors, unexpected behaviors, etc.
    | Critical
    -- ^ Used before shutting down the application.
    deriving (Show, Read, Eq, Ord)

instance Pretty.Pretty Severity where
    pretty = Pretty.pretty . show

class (Pretty entry, Typeable entry) => Entry entry where
    toEntry :: entry -> SomeEntry
    toEntry = SomeEntry

    fromEntry :: SomeEntry -> Maybe entry
    fromEntry (SomeEntry entry) = Data.Typeable.cast entry

    entrySeverity :: entry -> Severity

data SomeEntry where
    SomeEntry :: Entry entry => entry -> SomeEntry

instance Entry SomeEntry where
    entrySeverity (SomeEntry entry) = entrySeverity entry

instance Pretty SomeEntry where
    pretty (SomeEntry entry) = Pretty.pretty entry

someEntry :: (Entry e1, Entry e2) => Prism SomeEntry SomeEntry e1 e2
someEntry = Lens.prism' toEntry fromEntry

entryTypeText :: SomeEntry -> Text
entryTypeText (SomeEntry entry) =
    Text.pack . show . Reflection.typeOf $ entry
