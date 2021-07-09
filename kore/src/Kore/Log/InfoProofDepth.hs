{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Log.InfoProofDepth (
    InfoProofDepth (..),
    infoUnprovenDepth,
    infoProvenDepth,
    ProofDepth (..),
) where

import qualified Data.Semigroup as Semigroup
import Log
import Numeric.Natural (
    Natural,
 )
import Prelude.Kore
import Pretty (
    Pretty,
 )
import qualified Pretty

newtype ProofDepth = ProofDepth {getProofDepth :: Natural}
    deriving stock (Eq, Ord, Show)
    deriving newtype (Enum)
    deriving (Semigroup) via (Semigroup.Max Natural)

instance Pretty ProofDepth where
    pretty proofDepth =
        Pretty.hsep ["proof depth:", Pretty.pretty (getProofDepth proofDepth)]

data InfoProofDepth
    = InfoUnprovenDepth ProofDepth
    | InfoProvenDepth ProofDepth
    deriving stock (Show)

instance Pretty InfoProofDepth where
    pretty (InfoUnprovenDepth depth) =
        Pretty.hsep ["proof incomplete:", Pretty.pretty depth]
    pretty (InfoProvenDepth depth) =
        Pretty.hsep ["proof complete:", Pretty.pretty depth]

instance Entry InfoProofDepth where
    entrySeverity _ = Info
    helpDoc _ = "log depth of proof graph"

infoUnprovenDepth :: MonadLog log => ProofDepth -> log ()
infoUnprovenDepth = logEntry . InfoUnprovenDepth

infoProvenDepth :: MonadLog log => ProofDepth -> log ()
infoProvenDepth = logEntry . InfoProvenDepth
