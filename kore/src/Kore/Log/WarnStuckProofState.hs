{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.WarnStuckProofState
    ( WarnStuckProofState (..)
    , warnStuckProofStateTermsUnifiable
    , warnStuckProofStateTermsNotUnifiable
    ) where

import Prelude.Kore

import Log
import Pretty
    ( Pretty
    )
import qualified Pretty

{- | @WarnStuckProofState@ is emitted when a proof gets stuck.

The warning message distinguishes for the user the ways that a proof can be stuck.

 -}
data WarnStuckProofState
    = TermsUnifiableStuck
    -- ^ The terms of the left- and right-hand sides do not unify,
    -- and the left-hand side cannot be rewritten any further.
    | TermsNotUnifiableStuck
    -- ^ The left- and right-hand side terms are unifiable, but the left-hand side
    -- condition does not imply the right-hand side condition.
    deriving Show

instance Pretty WarnStuckProofState where
    pretty TermsUnifiableStuck =
        "The proof has reached the final configuration, but the claimed implication is not valid."
    pretty TermsNotUnifiableStuck =
        "The claim cannot be rewritten further, and the claimed implication is not valid."

instance Entry WarnStuckProofState where
    entrySeverity _ = Warning
    helpDoc _ = "warn when a proof state is stuck, distinguishing between the\
                \ two cases"

warnStuckProofStateTermsUnifiable :: MonadLog log => log ()
warnStuckProofStateTermsUnifiable = logEntry TermsUnifiableStuck

warnStuckProofStateTermsNotUnifiable :: MonadLog log => log ()
warnStuckProofStateTermsNotUnifiable = logEntry TermsNotUnifiableStuck
