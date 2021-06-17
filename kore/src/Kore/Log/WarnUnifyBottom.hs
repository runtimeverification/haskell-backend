{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.WarnUnifyBottom (
    WarnUnifyBottom (..),
    warnUnifyBottom,
    warnUnifyBottomAndReturnBottom,
) where

import Data.Text (
    Text,
 )
import Kore.Internal.TermLike (
    InternalVariable,
    TermLike (..),
 )
import Kore.Unparser (unparse)
import Log (
    Entry (..),
    MonadLog (..),
    Severity (..),
    logEntry,
 )
import Prelude.Kore
import Pretty (
    Pretty,
    pretty,
    unAnnotate,
 )
import qualified Pretty

data WarnUnifyBottom variable = WarnUnifyBottom
    { info :: Text
    , first :: TermLike variable
    , second :: TermLike variable
    }
    deriving stock (Show, Eq)

instance InternalVariable variable => Pretty (WarnUnifyBottom variable) where
    pretty (WarnUnifyBottom info first second) =
        Pretty.vsep
            [ unAnnotate $ pretty info
            , "When unifying:"
            , Pretty.indent 4 . unparse $ first
            , "With:\n"
            , Pretty.indent 4 . unparse $ second
            ]

instance InternalVariable variable => Entry (WarnUnifyBottom variable) where
    entrySeverity _ = Warning
    helpDoc _ = "TODO"

warnUnifyBottom ::
    MonadLog log =>
    InternalVariable variable =>
    Text ->
    TermLike variable ->
    TermLike variable ->
    log ()
warnUnifyBottom info first second =
    logEntry $ WarnUnifyBottom info first second

warnUnifyBottomAndReturnBottom ::
    MonadLog log =>
    Alternative log =>
    InternalVariable variable =>
    Text ->
    TermLike variable ->
    TermLike variable ->
    log a
warnUnifyBottomAndReturnBottom info first second = do
    warnUnifyBottom info first second
    empty