{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Log.InfoExecDepth (
    InfoExecDepth (..),
    ExecDepth (..),
    infoExecDepth,
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
    helpDoc _ = "log depth of execution graph"

infoExecDepth :: MonadLog log => ExecDepth -> log ()
infoExecDepth = logEntry . InfoExecDepth
