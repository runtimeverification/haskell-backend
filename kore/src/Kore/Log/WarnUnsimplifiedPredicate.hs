{- |
Copyright   : (c) Runtime Verification, 2021
License     : BSD-3-Clause
-}
module Kore.Log.WarnUnsimplifiedPredicate (
    WarnUnsimplifiedPredicate (..),
    warnUnsimplifiedPredicate,
) where

import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import Kore.Internal.MultiOr (
    MultiOr,
 )
import Kore.Internal.Predicate (
    Predicate,
 )
import Kore.Rewriting.RewritingVariable
import Log
import Prelude.Kore
import Pretty (
    Pretty,
 )
import qualified Pretty

data WarnUnsimplifiedPredicate = WarnUnsimplifiedPredicate
    { limit :: !Int
    , original :: !(Predicate RewritingVariableName)
    , output :: !(MultiOr (MultiAnd (Predicate RewritingVariableName)))
    }
    deriving stock (Show)

instance Pretty WarnUnsimplifiedPredicate where
    pretty WarnUnsimplifiedPredicate{original, output, limit} =
        Pretty.vsep
            [ Pretty.hsep
                [ "Predicate not simplified after"
                , Pretty.pretty limit
                , "rounds."
                ]
            , "Original predicate:"
            , (Pretty.indent 4) (Pretty.pretty original)
            , Pretty.hsep
                [ "Output after"
                , Pretty.pretty limit
                , "rounds:"
                ]
            , (Pretty.indent 4) (Pretty.pretty output)
            ]

instance Entry WarnUnsimplifiedPredicate where
    entrySeverity _ = Warning
    helpDoc _ = "warn when a predicate is not simplified"

warnUnsimplifiedPredicate ::
    MonadLog log =>
    Int ->
    Predicate RewritingVariableName ->
    MultiOr (MultiAnd (Predicate RewritingVariableName)) ->
    log ()
warnUnsimplifiedPredicate limit original output =
    logEntry WarnUnsimplifiedPredicate{limit, original, output}
