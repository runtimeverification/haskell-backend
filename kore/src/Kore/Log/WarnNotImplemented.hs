{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.WarnNotImplemented (
    WarnNotImplemented (..),
    warnNotImplemented,
) where

import Kore.Internal.TermLike
import Kore.Unparser
import Log
import Prelude.Kore
import Pretty (
    Pretty,
 )
import qualified Pretty

newtype WarnNotImplemented variable = WarnNotImplemented {notImplementedTerm :: TermLike variable}
    deriving stock (Show)

instance InternalVariable variable => Pretty (WarnNotImplemented variable) where
    pretty (WarnNotImplemented term) =
        Pretty.vsep
            [ "The following term is an argument to a builtin function that is not implemented on it:"
            , unparse term
            ]

instance InternalVariable variable => Entry (WarnNotImplemented variable) where
    entrySeverity _ = Warning
    helpDoc _ = "warn when we try to evaluate a partial builtin function on unimplemented cases"

warnNotImplemented ::
    MonadLog log =>
    InternalVariable variable =>
    TermLike variable ->
    log ()
warnNotImplemented = logEntry . WarnNotImplemented
