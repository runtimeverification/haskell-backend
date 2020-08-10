{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.WarnTrivialClaim
    ( WarnTrivialClaim (..)
    , warnProvenClaimZeroDepth
    , warnTrivialClaimRemoved
    ) where

import Prelude.Kore

import Kore.Attribute.SourceLocation
import Kore.Log.InfoProofDepth
import Kore.Step.RulePattern
import Log
import Pretty
    ( Pretty
    )
import qualified Pretty

data WarnTrivialClaim
    = WarnProvenClaimZeroDepth ReachabilityRule
    | WarnTrivialClaimRemoved ReachabilityRule
    deriving Show

instance Pretty WarnTrivialClaim where
    pretty (WarnProvenClaimZeroDepth rule) =
        Pretty.hsep
            [ "claim proven without taking any steps:"
            , Pretty.pretty (from rule :: SourceLocation)
            ]
    pretty (WarnTrivialClaimRemoved rule) =
        Pretty.hsep
            [ "trivial claim removed:"
            , Pretty.pretty (from rule :: SourceLocation)
            ]


instance Entry WarnTrivialClaim where
    entrySeverity _ = Warning
    helpDoc _ =
        "warn when a claim is removed or proven without taking any steps"

warnProvenClaimZeroDepth
    :: MonadLog log
    => ProofDepth
    -> ReachabilityRule
    -> log ()
warnProvenClaimZeroDepth (ProofDepth depth) rule =
    when (depth == 0) $ logEntry (WarnProvenClaimZeroDepth rule)

warnTrivialClaimRemoved
    :: MonadLog log
    => ReachabilityRule
    -> log ()
warnTrivialClaimRemoved rule =
    logEntry (WarnTrivialClaimRemoved rule)
