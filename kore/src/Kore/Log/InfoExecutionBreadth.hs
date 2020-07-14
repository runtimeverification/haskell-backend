{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}

module Kore.Log.InfoExecutionBreadth
    ( InfoExecutionBreadth
    , infoExecutionBreadth
    ) where

import Prelude.Kore

import Pretty
    ( Pretty
    )
import Log
import qualified Pretty
import Numeric.Natural  

type ExecutionBreadth = Natural

newtype InfoExecutionBreadth =
    InfoExecutionBreadth { breadth :: ExecutionBreadth }
    deriving (Show)

instance Pretty InfoExecutionBreadth where
    pretty (InfoExecutionBreadth breadth) =
        Pretty.hsep
            [ "Number of concurrent branches:"
            , Pretty.pretty breadth
            ]

instance Entry InfoExecutionBreadth where
    entrySeverity _ = Info
    helpDoc _ = "log number of concurrent branches"

infoExecutionBreadth
    :: MonadLog log
    => Integral breadth
    => breadth
    -> log ()
infoExecutionBreadth =
    logEntry . InfoExecutionBreadth . fromIntegral