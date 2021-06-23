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
    VariableName,
 )
import qualified Kore.Internal.TermLike as TermLike
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

data WarnUnifyBottom = WarnUnifyBottom
    { info :: Text
    , first :: TermLike VariableName
    , second :: TermLike VariableName
    }
    deriving stock (Show, Eq)

instance Pretty WarnUnifyBottom where
    pretty (WarnUnifyBottom info first second) =
        Pretty.vsep
            [ unAnnotate $ pretty info
            , "When unifying:"
            , Pretty.indent 4 . unparse $ first
            , "With:"
            , Pretty.indent 4 . unparse $ second
            ]

instance Entry WarnUnifyBottom where
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
    logEntry $
        WarnUnifyBottom
            info
            (TermLike.mapVariables (pure $ from @_ @VariableName) first)
            (TermLike.mapVariables (pure $ from @_ @VariableName) second)

warnUnifyBottomAndReturnBottom ::
    MonadLog log =>
    Alternative log =>
    InternalVariable variable =>
    Text ->
    TermLike variable ->
    TermLike variable ->
    log a
warnUnifyBottomAndReturnBottom info first second = do
    warnUnifyBottom
        info
        (TermLike.mapVariables (pure $ from @_ @VariableName) first)
        (TermLike.mapVariables (pure $ from @_ @VariableName) second)
    empty
