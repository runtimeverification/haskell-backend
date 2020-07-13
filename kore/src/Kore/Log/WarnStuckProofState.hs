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

import Pretty
    ( Pretty
    )
import qualified Pretty
import Log

data WarnStuckProofState
    = TermsUnifiableStuck
    -- ^ The terms of the left- and right-hand sides do not unify,
    -- and the left-hand side cannot be rewritten any further
    | TermsNotUnifiableStuck
    -- ^ The left- and right-hand side are unifiable, but the left-hand side
    -- condition does not imply the right-hand side condition
    deriving Show

instance Pretty WarnStuckProofState where
    pretty TermsUnifiableStuck =
        "Can't apply any more rules"
    pretty TermsNotUnifiableStuck =
        "The LHS side condition does not imply the RHS side condition"

instance Entry WarnStuckProofState where
    entrySeverity _ = Warning
    helpDoc _ = "warn when a proof state is stuck, distinguishing between the\
                \ two cases"

warnStuckProofStateTermsUnifiable :: MonadLog log => log ()
warnStuckProofStateTermsUnifiable = logEntry TermsUnifiableStuck

warnStuckProofStateTermsNotUnifiable :: MonadLog log => log ()
warnStuckProofStateTermsNotUnifiable = logEntry TermsNotUnifiableStuck