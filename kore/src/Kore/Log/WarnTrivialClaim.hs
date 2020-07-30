{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Log.WarnTrivialClaim
    ( WarnTrivialClaim (..)
    , warnIfProvenWithZeroDepth
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
    = WarnProvenClaimZeroDepth
    | WarnTrivialClaimRemoved ReachabilityRule
    deriving Show

instance Pretty WarnTrivialClaim where
    pretty WarnProvenClaimZeroDepth =
        Pretty.hsep
            [ "claim proven without taking any steps:"
            ]
    pretty (WarnTrivialClaimRemoved rule) =
        Pretty.hsep
            [ "trivial claim removed:"
            , Pretty.pretty $ show (from rule :: SourceLocation)
            ]


instance Entry WarnTrivialClaim where
    entrySeverity _ = Warning
    helpDoc _ =
        "warn when a claim is removed or proven without taking any steps"

warnIfProvenWithZeroDepth
    :: MonadLog log
    => ProofDepth
    -> log ()
warnIfProvenWithZeroDepth (ProofDepth depth) =
    when (depth == 0) $ logEntry WarnProvenClaimZeroDepth

warnTrivialClaimRemoved
    :: MonadLog log
    => ReachabilityRule
    -> log ()
warnTrivialClaimRemoved rule =
    logEntry (WarnTrivialClaimRemoved rule)
