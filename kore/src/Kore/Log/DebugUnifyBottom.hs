{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.DebugUnifyBottom (
    DebugUnifyBottom (..),
    debugUnifyBottom,
    debugUnifyBottomAndReturnBottom,
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

data DebugUnifyBottom = DebugUnifyBottom
    { info :: Text
    , first :: TermLike VariableName
    , second :: TermLike VariableName
    }
    deriving stock (Show, Eq)

instance Pretty DebugUnifyBottom where
    pretty (DebugUnifyBottom info first second) =
        Pretty.vsep
            [ unAnnotate $ pretty info
            , "When unifying:"
            , Pretty.indent 4 . unparse $ first
            , "With:"
            , Pretty.indent 4 . unparse $ second
            ]

instance Entry DebugUnifyBottom where
    entrySeverity _ = Debug
    helpDoc _ = "log failed unification"

debugUnifyBottom ::
    MonadLog log =>
    InternalVariable variable =>
    Text ->
    TermLike variable ->
    TermLike variable ->
    log ()
debugUnifyBottom info first second =
    logEntry $
        DebugUnifyBottom
            info
            (TermLike.mapVariables (pure $ from @_ @VariableName) first)
            (TermLike.mapVariables (pure $ from @_ @VariableName) second)

debugUnifyBottomAndReturnBottom ::
    MonadLog log =>
    Alternative log =>
    InternalVariable variable =>
    Text ->
    TermLike variable ->
    TermLike variable ->
    log a
debugUnifyBottomAndReturnBottom info first second = do
    debugUnifyBottom
        info
        (TermLike.mapVariables (pure $ from @_ @VariableName) first)
        (TermLike.mapVariables (pure $ from @_ @VariableName) second)
    empty
