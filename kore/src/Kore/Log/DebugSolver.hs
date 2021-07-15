{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Log.DebugSolver (
    DebugSolverSend (..),
    DebugSolverRecv (..),
    logDebugSolverSendWith,
    logDebugSolverRecvWith,
    DebugSolverOptions (..),
    emptyDebugSolverOptions,
    parseDebugSolverOptions,
    solverTranscriptLogger,
) where

import Data.Default
import Data.Text (
    Text,
 )
import qualified Data.Text.Lazy as Text.Lazy
import qualified Data.Text.Lazy.Builder as Text.Lazy.Builder
import Log (
    ActualEntry (..),
    Entry (..),
    LogAction (..),
    Severity (Debug),
    SomeEntry,
    logWith,
 )
import Options.Applicative (
    Parser,
    help,
    long,
    strOption,
 )
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import SMT.AST (
    SExpr (..),
 )
import qualified SMT.AST as SMT

newtype DebugSolverSend = DebugSolverSend
    { getSendSExpr :: SExpr
    }
    deriving stock (Show)

newtype DebugSolverRecv = DebugSolverRecv
    { getRecvSExpr :: Text
    }
    deriving stock (Show)

instance Pretty DebugSolverSend where
    pretty DebugSolverSend{getSendSExpr} =
        pretty . SMT.buildText $ getSendSExpr

instance Pretty DebugSolverRecv where
    pretty DebugSolverRecv{getRecvSExpr} =
        pretty getRecvSExpr

instance Entry DebugSolverSend where
    entrySeverity _ = Debug
    helpDoc _ = "log commands sent to SMT solver"

instance Entry DebugSolverRecv where
    entrySeverity _ = Debug
    helpDoc _ = "log responses received from SMT solver"

logDebugSolverSendWith ::
    LogAction m SomeEntry ->
    SExpr ->
    m ()
logDebugSolverSendWith logger sExpr =
    logWith logger $ DebugSolverSend sExpr

logDebugSolverRecvWith ::
    LogAction m SomeEntry ->
    Text ->
    m ()
logDebugSolverRecvWith logger smtText =
    logWith logger $ DebugSolverRecv smtText

solverTranscriptLogger ::
    Applicative m =>
    LogAction m Text ->
    LogAction m ActualEntry
solverTranscriptLogger textLogger =
    LogAction action
  where
    action ActualEntry{actualEntry}
        | Just sendEntry <- matchDebugSolverSend actualEntry =
            unLogAction textLogger (sentText sendEntry)
        | Just recvEntry <- matchDebugSolverRecv actualEntry =
            unLogAction textLogger (receivedText recvEntry)
        | otherwise =
            pure ()
      where
        sentText :: DebugSolverSend -> Text
        sentText (DebugSolverSend sexpr) =
            let builder = SMT.buildSExpr sexpr
             in (Text.Lazy.toStrict . Text.Lazy.Builder.toLazyText) builder
        receivedText :: DebugSolverRecv -> Text
        receivedText (DebugSolverRecv text) = "; " <> text

matchDebugSolverSend :: SomeEntry -> Maybe DebugSolverSend
matchDebugSolverSend = fromEntry

matchDebugSolverRecv :: SomeEntry -> Maybe DebugSolverRecv
matchDebugSolverRecv = fromEntry

{- | Options (from the command-line) specifying where to create a solver
transcript.

See also: 'parseDebugSolverOptions'
-}
newtype DebugSolverOptions = DebugSolverOptions
    { logFile :: Maybe FilePath
    }
    deriving stock (Eq, Show)

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
emptyDebugSolverOptions = DebugSolverOptions{logFile = Nothing}
