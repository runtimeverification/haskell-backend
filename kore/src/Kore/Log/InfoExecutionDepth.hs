{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

module Kore.Log.InfoExecutionDepth
    ( InfoExecutionDepth (..)
    , infoUnprovenDepth
    , infoProvenDepth
    , infoExecutionDepth
    ) where

import Prelude.Kore

import Kore.Strategies.ProofState
import Log
import Pretty
    ( Pretty
    )
import qualified Pretty

data InfoExecutionDepth
    = UnprovenConfiguration ExecutionDepth
    | LongestProvenClaim ExecutionDepth
    | ExecutionLength ExecutionDepth
    deriving Show

instance Pretty InfoExecutionDepth where
    pretty (UnprovenConfiguration depth) =
        Pretty.hsep
            [ "Final execution length of an unproven configuration:"
            , Pretty.pretty (getDepth depth)
            ]
    pretty (LongestProvenClaim depth) =
        Pretty.hsep
            [ "Final execution length of the longest proven claim:"
            , Pretty.pretty (getDepth depth)
            ]
    pretty (ExecutionLength depth) =
        Pretty.hsep
            [ "Final execution length:"
            , Pretty.pretty (getDepth depth)
            ]

instance Entry InfoExecutionDepth where
    entrySeverity _ = Info
    helpDoc _ = "log execution or proof length"

infoUnprovenDepth :: MonadLog log => ExecutionDepth -> log ()
infoUnprovenDepth depth = logEntry . UnprovenConfiguration $ depth

infoProvenDepth :: MonadLog log => ExecutionDepth -> log ()
infoProvenDepth depth = logEntry . LongestProvenClaim $ depth

infoExecutionDepth :: MonadLog log => ExecutionDepth -> log ()
infoExecutionDepth = logEntry . ExecutionLength
