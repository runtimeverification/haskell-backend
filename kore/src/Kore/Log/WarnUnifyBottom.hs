{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.WarnUnifyBottom (
    WarnUnifyBottom (..),
    warnUnifyBottom,
) where

import Kore.Internal.TermLike (
    InternalVariable,
    TermLike (..),
 )
import Kore.Log (
    MonadLog,
    Severity (..),
 )
import Kore.Unparser (unparse)
import Log (
    Entry (..),
    logEntry,
 )
import Prelude.Kore
import Pretty (
    Doc,
    Pretty,
    unAnnotate,
 )
import qualified Pretty

data WarnUnifyBottom variable = WarnUnifyBottom
    { info :: Doc ()
    , first :: TermLike variable
    , second :: TermLike variable
    }
    deriving stock (Show)

instance InternalVariable variable => Pretty (WarnUnifyBottom variable) where
    pretty (WarnUnifyBottom info first second) =
        Pretty.vsep
            [ unAnnotate info
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
    Doc () ->
    TermLike variable ->
    TermLike variable ->
    log ()
warnUnifyBottom info first second =
    logEntry $ WarnUnifyBottom info first second