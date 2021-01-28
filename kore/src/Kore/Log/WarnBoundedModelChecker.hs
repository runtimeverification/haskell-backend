{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.WarnBoundedModelChecker
    ( WarnBoundedModelChecker (..)
    , warnBoundedModelChecker
    ) where

import Prelude.Kore

import Kore.Attribute.SourceLocation
import Kore.Internal.TermLike
import Kore.Step.RulePattern
    ( ImplicationRule
    )
import Log
import Pretty
    ( Pretty
    )
import qualified Pretty

newtype WarnBoundedModelChecker
    = WarnBoundedModelChecker (ImplicationRule VariableName)
    deriving Show

instance Pretty WarnBoundedModelChecker where
    pretty (WarnBoundedModelChecker claim) =
        Pretty.hsep
            [ "The pattern does not terminate within the bound at:"
            , Pretty.pretty (from claim :: SourceLocation)
            ]

instance Entry WarnBoundedModelChecker where
    entrySeverity _ = Warning
    helpDoc _ = "warn when the bounded model checker does not terminate within the given bound"

warnBoundedModelChecker
    :: MonadLog log
    => ImplicationRule VariableName
    -> log ()
warnBoundedModelChecker claim =
    logEntry (WarnBoundedModelChecker claim)
