{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
{-# LANGUAGE Strict #-}

module Kore.Log.WarnStuckClaimState
    ( WarnStuckClaimState (..)
    , warnStuckClaimStateTermsUnifiable
    , warnStuckClaimStateTermsNotUnifiable
    ) where

import Prelude.Kore

import Kore.Attribute.SourceLocation
import Kore.Reachability.SomeClaim
import Log
import Pretty
    ( Pretty
    )
import qualified Pretty

{- | @WarnStuckClaimState@ is emitted when a proof gets stuck.

The warning message distinguishes for the user the ways that a proof can be stuck.

 -}
data WarnStuckClaimState
    = TermsUnifiableStuck !SomeClaim
    -- ^ The terms of the left- and right-hand sides do not unify,
    -- and the left-hand side cannot be rewritten any further.
    | TermsNotUnifiableStuck !SomeClaim
    -- ^ The left- and right-hand side terms are unifiable, but the left-hand side
    -- condition does not imply the right-hand side condition.
    deriving Show

instance Pretty WarnStuckClaimState where
    pretty (TermsUnifiableStuck claim) =
        Pretty.hsep
            [ "The proof has reached the final configuration, but the claimed implication is not valid. Location:"
            , Pretty.pretty (from claim :: SourceLocation)
            ]
    pretty (TermsNotUnifiableStuck claim) =
        Pretty.hsep
            [ "The claim cannot be rewritten further, and the claimed implication is not valid."
            , Pretty.pretty (from claim :: SourceLocation)
            ]

instance Entry WarnStuckClaimState where
    entrySeverity _ = Warning
    helpDoc _ = "distinguish the ways a proof can become stuck"

warnStuckClaimStateTermsUnifiable :: MonadLog log => SomeClaim -> log ()
warnStuckClaimStateTermsUnifiable = logEntry . TermsUnifiableStuck

warnStuckClaimStateTermsNotUnifiable :: MonadLog log => SomeClaim -> log ()
warnStuckClaimStateTermsNotUnifiable = logEntry . TermsNotUnifiableStuck
