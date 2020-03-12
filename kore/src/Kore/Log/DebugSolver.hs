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

    , solverTranscriptLogger
    ) where

import Prelude.Kore

import Data.Default
import Data.Text
    ( Text
    )
import Data.Text.Prettyprint.Doc
    ( Pretty (..)
    )
import qualified Data.Text.Prettyprint.Doc as Pretty
    ( defaultLayoutOptions
    , layoutPretty
    )
import qualified Data.Text.Prettyprint.Doc.Render.Text as Pretty
    ( renderStrict
    )
import Options.Applicative
    ( Parser
    , help
    , long
    , strOption
    )

import Log
    ( ActualEntry (..)
    , Entry (..)
    , LogAction (..)
    , Severity (Debug)
    , SomeEntry
    , logWith
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

logDebugSolverSendWith
    :: LogAction m ActualEntry
    -> SExpr
    -> m ()
logDebugSolverSendWith logger sExpr =
    logWith logger $ DebugSolverSend sExpr

logDebugSolverRecvWith
    :: LogAction m ActualEntry
    -> Text
    -> m ()
logDebugSolverRecvWith logger smtText =
    logWith logger $ DebugSolverRecv smtText

solverTranscriptLogger
    :: Applicative m
    => LogAction m Text
    -> LogAction m ActualEntry
solverTranscriptLogger textLogger =
    LogAction
    $ \ActualEntry { actualEntry } ->
        case matchDebugSolverSend actualEntry of
            Just sendEntry ->
                unLogAction textLogger (messageToText sendEntry)
            Nothing -> unLogAction mempty actualEntry
  where
    messageToText :: DebugSolverSend -> Text
    messageToText =
        Pretty.renderStrict
        . Pretty.layoutPretty Pretty.defaultLayoutOptions
        . pretty

matchDebugSolverSend :: SomeEntry -> Maybe DebugSolverSend
matchDebugSolverSend = fromEntry

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
