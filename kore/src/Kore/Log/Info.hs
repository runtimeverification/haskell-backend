{- |
Copyright : (c) Runtime Verification, 2020-2021
License   : BSD-3-Clause
-}
module Kore.Log.Info (
    -- * InfoAttemptUnification
    InfoAttemptUnification (..),
    infoAttemptUnification,

    -- * InfoExecBreadth
    InfoExecBreadth,
    ExecBreadth (..),
    infoExecBreadth,

    -- * InfoExecDepth
    InfoExecDepth (..),
    ExecDepth (..),
    infoExecDepth,

    -- * InfoProofDepth
    InfoProofDepth (..),
    infoUnprovenDepth,
    infoProvenDepth,
    ProofDepth (..),

    -- * InfoReachability
    InfoReachability (..),
    whileReachability,
) where

import qualified Data.Semigroup as Semigroup
import qualified GHC.Generics as GHC
import qualified Generics.SOP as SOP
import Kore.Internal.TermLike (
    InternalVariable,
    TermLike,
    VariableName,
    toVariableName,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Reachability.Prim (
    Prim (..),
 )
import Kore.Unparser (
    unparse,
 )
import Log (
    Entry,
    MonadLog,
    Severity (..),
    logEntry,
    logWhile,
 )
import qualified Log
import Numeric.Natural (
    Natural,
 )
import Prelude.Kore
import Pretty (
    Doc,
    Pretty,
    (<+>),
 )
import qualified Pretty

-- | InfoAttemptUnification
data InfoAttemptUnification = InfoAttemptUnification {term1, term2 :: TermLike VariableName}
    deriving stock (Show)
    deriving stock (GHC.Generic)
    deriving anyclass (SOP.Generic, SOP.HasDatatypeInfo)

instance Entry InfoAttemptUnification where
    entrySeverity _ = Info
    contextDoc _ = Just "while attempting unification"
    oneLineDoc _ = "InfoAttemptUnification"
    helpDoc _ = "log unification attempts"

instance Pretty InfoAttemptUnification where
    pretty InfoAttemptUnification{term1, term2} =
        Pretty.vsep
            [ "Attempting to unify"
            , Pretty.indent 4 $ unparse term1
            , Pretty.indent 2 "with"
            , Pretty.indent 4 $ unparse term2
            ]

infoAttemptUnification ::
    MonadLog log =>
    InternalVariable variable =>
    TermLike variable ->
    TermLike variable ->
    log a ->
    log a
infoAttemptUnification term1' term2' =
    logWhile InfoAttemptUnification{term1, term2}
  where
    mapVariables = TermLike.mapVariables (pure toVariableName)
    term1 = mapVariables term1'
    term2 = mapVariables term2'

-- | InfoExecBreadth
newtype ExecBreadth = ExecBreadth {getExecBreadth :: Natural}
    deriving stock (Show)

instance Pretty ExecBreadth where
    pretty = Pretty.pretty . getExecBreadth

newtype InfoExecBreadth = InfoExecBreadth {breadth :: ExecBreadth}
    deriving stock (Show)

instance Pretty InfoExecBreadth where
    pretty (InfoExecBreadth breadth) =
        Pretty.hsep
            [ "number of concurrent branches:"
            , Pretty.pretty breadth
            ]

instance Entry InfoExecBreadth where
    entrySeverity _ = Info
    oneLineDoc (InfoExecBreadth (ExecBreadth execBreadth)) =
        Pretty.pretty execBreadth
    helpDoc _ = "log number of concurrent branches"

infoExecBreadth :: MonadLog log => ExecBreadth -> log ()
infoExecBreadth = logEntry . InfoExecBreadth

-- | InfoExecDepth
newtype ExecDepth = ExecDepth {getExecDepth :: Natural}
    deriving stock (Eq, Ord, Show)
    deriving newtype (Enum)
    deriving (Semigroup) via (Semigroup.Max Natural)

instance Pretty ExecDepth where
    pretty execDepth =
        Pretty.hsep ["exec depth:", Pretty.pretty (getExecDepth execDepth)]

data InfoExecDepth = InfoExecDepth ExecDepth
    deriving stock (Show)

instance Pretty InfoExecDepth where
    pretty (InfoExecDepth execDepth) =
        Pretty.hsep ["execution complete:", Pretty.pretty execDepth]

instance Entry InfoExecDepth where
    entrySeverity _ = Info
    oneLineDoc (InfoExecDepth (ExecDepth execDepth)) = Pretty.pretty execDepth
    helpDoc _ = "log depth of execution graph"

infoExecDepth :: MonadLog log => ExecDepth -> log ()
infoExecDepth = logEntry . InfoExecDepth

-- | InfoProofDepth
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
    oneLineDoc (InfoUnprovenDepth (ProofDepth depth)) =
        Pretty.hsep
            [ "InfoUnprovenDepth"
            , Pretty.colon
            , Pretty.pretty depth
            ]
    oneLineDoc (InfoProvenDepth (ProofDepth depth)) =
        Pretty.hsep
            [ "InfoProvenDepth"
            , Pretty.colon
            , Pretty.pretty depth
            ]

    helpDoc _ = "log depth of proof graph"

infoUnprovenDepth :: MonadLog log => ProofDepth -> log ()
infoUnprovenDepth = logEntry . InfoUnprovenDepth

infoProvenDepth :: MonadLog log => ProofDepth -> log ()
infoProvenDepth = logEntry . InfoProvenDepth

-- | InfoReachability
newtype InfoReachability = InfoReachability {prim :: Prim}
    deriving stock (Show)

instance Pretty InfoReachability where
    pretty InfoReachability{prim} =
        (Pretty.hsep . catMaybes) [primDoc prim]

instance Log.Entry InfoReachability where
    entrySeverity _ = Log.Info
    contextDoc InfoReachability{prim} = (<+>) "while" <$> primDoc prim
    oneLineDoc InfoReachability{prim} = Pretty.pretty . show $ prim
    helpDoc _ = "log reachability proof steps"

primDoc :: Prim -> Maybe (Doc ann)
primDoc Simplify = Just "simplifying the claim"
primDoc CheckImplication = Just "checking the implication"
primDoc ApplyClaims = Just "applying claims"
primDoc ApplyAxioms = Just "applying axioms"
primDoc _ = Nothing

whileReachability ::
    Log.MonadLog log =>
    Prim ->
    log a ->
    log a
whileReachability prim log
    | Just _ <- primDoc prim = Log.logWhile InfoReachability{prim} log
    | otherwise = log
