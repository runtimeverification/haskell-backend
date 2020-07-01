{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

module Kore.Log.InfoProofLength
    ( InfoProofLength
    , infoProofLength
    ) where

import Prelude.Kore

import Control.Monad
import Control.Error
    ( maximumMay
    )
import Numeric.Natural
    ( Natural
    )
import Kore.Strategies.ProofState
import Log
import Pretty
    ( Pretty
    )
import qualified Pretty

data InfoProofLength = UnprovenConfiguration Depth | LongestProvenClaim Depth
    deriving Show

instance Pretty InfoProofLength where
    pretty (UnprovenConfiguration depth) =
        Pretty.hsep
            [ "Final execution length of the longest proven claim: "
            , Pretty.pretty (getDepth depth)
            ]
    pretty (LongestProvenClaim depth) =
        Pretty.hsep
            [ "Final execution length of an unproven configuration: "
            , Pretty.pretty (getDepth depth)
            ]

instance Entry InfoProofLength where
    entrySeverity _ = Info
    helpDoc _ = "log proof length"

infoProofLength
    :: MonadLog log
    => [ProofState goal]
    -> log ()
infoProofLength proofStateList =
    case depthLongestProven proofStateList of
        Just n -> logEntry (LongestProvenClaim (Depth n))
        _ -> forM_ (depthSomeUnproven proofStateList)
            (logEntry . UnprovenConfiguration . Depth )
  where
    depthLongestProven :: [ProofState goal] -> Maybe Natural
    depthLongestProven proofStates =
        proofStates
        & filter isProven
        & fmap (getDepth . extractDepth)
        & maximumMay

    depthSomeUnproven :: [ProofState goal] -> Maybe Natural
    depthSomeUnproven proofStates =
        proofStates
        & filter (not . isProven)
        & fmap (getDepth . extractDepth)
        & headMay