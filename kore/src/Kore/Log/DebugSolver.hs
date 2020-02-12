{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}

module Kore.Log.DebugSolver
    ( DebugSolverSend (..)
    , DebugSolverRecv (..)
    , logDebugSolverSendWith
    , logDebugSolverRecvWith

    , DebugSolverOptions (..)
    , emptyDebugSolverOptions
    , parseDebugSolverOptions
    ) where

import Prelude.Kore

import Data.Default
import Data.Text
    ( Text
    )
import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )
import Options.Applicative
    ( Parser
    , help
    , long
    , strOption
    )

import Log
    ( Entry (..)
    , MonadLog
    , Severity (Debug)
    , logEntry
    )
import SMT.AST
    ( SExpr (..)
    )
import qualified SMT.AST as SMT

newtype DebugSolverSend =
    DebugSolverSend
        { getSendSExpr :: SExpr
        }

newtype DebugSolverRecv =
    DebugSolverRecv
        { getRecvSExpr :: Text
        }

instance Pretty DebugSolverSend where
    pretty DebugSolverSend { getSendSExpr } =
        pretty . SMT.buildText $ getSendSExpr

instance Pretty DebugSolverRecv where
    pretty DebugSolverRecv { getRecvSExpr } =
        pretty getRecvSExpr

instance Entry DebugSolverSend where
    entrySeverity _ = Debug

instance Entry DebugSolverRecv where
    entrySeverity _ = Debug

logDebugSolverSendWith :: MonadLog m => SExpr -> m ()
logDebugSolverSendWith sExpr =
    logEntry $ DebugSolverSend sExpr

logDebugSolverRecvWith :: MonadLog m => Text -> m ()
logDebugSolverRecvWith smtText =
    logEntry $ DebugSolverRecv smtText

{- | Options (from the command-line) specifying where to create a solver
transcript.

See also: 'parseDebugSolverOptions'

-}
newtype DebugSolverOptions =
    DebugSolverOptions
        { logFile :: Maybe FilePath
        }
    deriving (Eq, Show)

instance Default DebugSolverOptions where
    def = DebugSolverOptions Nothing

parseDebugSolverOptions :: Parser DebugSolverOptions
parseDebugSolverOptions =
    (DebugSolverOptions . Just <$> parseLogFile)
    <|> pure (def @DebugSolverOptions)
  where
    parseLogFile =
        let info =
                long "solver-transcript"
                <> help "Name of the file for the SMT solver transcript."
        in strOption info

emptyDebugSolverOptions :: DebugSolverOptions
emptyDebugSolverOptions = DebugSolverOptions {logFile = Nothing}
