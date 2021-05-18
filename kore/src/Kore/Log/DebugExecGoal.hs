{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA
-}
module Kore.Log.DebugExecGoal (
    DebugExecGoal (..),
    debugExecGoal,
) where

import Kore.Internal.TermLike (
    TermLike,
 )
import Kore.Internal.Variable (
    VariableName,
 )
import Kore.Unparser (
    unparseToCompactString,
 )
import Log
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import qualified Pretty

data DebugExecGoal
    = DebugExecGoal (TermLike VariableName) (TermLike VariableName)
    deriving (Show)

instance Pretty DebugExecGoal where
    pretty (DebugExecGoal initial final) =
        Pretty.vsep $
            pretty
                <$> [ "task: rewriting" :: String
                    , "initial: >"
                    , "  " ++ unparseToCompactString initial
                    , "final: >"
                    , "  " ++ unparseToCompactString final
                    ]

instance Entry DebugExecGoal where
    entrySeverity _ = Debug
    helpDoc _ = "log initial and final configuration"

debugExecGoal ::
    MonadLog log =>
    TermLike VariableName ->
    TermLike VariableName ->
    log ()
debugExecGoal initial final =
    logEntry (DebugExecGoal initial final)
