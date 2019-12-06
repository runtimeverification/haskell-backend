{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Logger.DebugSolver
    ( logDebugSolverSendWith
    , logDebugSolverRecvWith
    ) where

import Data.Text
    ( Text
    )
import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )

import Kore.Logger
    ( Entry (..)
    , LogAction
    , Severity (Debug)
    , SomeEntry
    , logWith
    )

newtype DebugSolverSend =
    DebugSolverSend
        { getSendSExpr :: Text
        }

newtype DebugSolverRecv =
    DebugSolverRecv
        { getRecvSExpr :: Text
        }

instance Pretty DebugSolverSend where
    pretty DebugSolverSend { getSendSExpr } =
        pretty getSendSExpr

instance Pretty DebugSolverRecv where
    pretty DebugSolverRecv { getRecvSExpr } =
        pretty getRecvSExpr

instance Entry DebugSolverSend where
    entrySeverity _ = Debug
    entryScopes _ = mempty

instance Entry DebugSolverRecv where
    entrySeverity _ = Debug
    entryScopes _ = mempty

logDebugSolverSendWith
    :: LogAction m SomeEntry
    -> Text
    -> m ()
logDebugSolverSendWith logger smtText =
    logWith logger $ DebugSolverSend smtText

logDebugSolverRecvWith
    :: LogAction m SomeEntry
    -> Text
    -> m ()
logDebugSolverRecvWith logger smtText =
    logWith logger $ DebugSolverRecv smtText
