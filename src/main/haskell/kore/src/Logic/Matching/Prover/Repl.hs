{-|
Description: A simple textual interface for building a proof

A simple textual interface for building a proof, offering commands
directly corresponding to the 'Kore.MatchingLogic.HilbertProof' API.
Parsers must be provided for the formulas, rules, and labels of
a particular instance of 'ProofSystem'.
-}
module Logic.Matching.Prover.Repl
  ( ProverState(..)
  , ProverEnv(..)
  , runProver
  , execReplT
  , defaultSettings )
where

import Control.Monad
       ( when )
import Control.Monad.Reader
       ( reader )
import Control.Monad.State.Strict
       ( get, gets, modify, put )

import qualified Data.Map.Strict as Map
import           Data.Sequence
                 ( Seq ((:|>)) )

import Data.Text.Prettyprint.Doc
       ( Pretty (pretty) )
import Text.Megaparsec
       ( parse, parseErrorPretty )

import Kore.Error
import Kore.Parser.ParserUtils ()

import           Logic.Matching.Prover.Command
                 ( Command (..), Parser )
import           Logic.Matching.Prover.Repl.Class
                 ( MonadHaskeline (..), MonadRepl, defaultSettings, execReplT )
import           Logic.Proof.Hilbert
                 ( Proof (..), ProofSystem (..) )
import qualified Logic.Proof.Hilbert as Hilbert

-- | Stack of commands executed by the prover
type CommandStack ix rule formula = [Command ix rule formula]

-- | Environment bindings for use in the prover
data ProverEnv ix rule formula error =
  ProverEnv
  { commandParser   :: !(Parser (Command ix rule formula))
  -- ^ Prover command parser
  , formulaVerifier :: !(formula -> Either (Error error) ())
  -- ^ function for matching logic well-formedness verification
  }

-- | Mutable state of the prover, containing the proof in
--   progress and the command stack that built it.
data ProverState ix rule formula =
  ProverState
  { proofState :: (Proof ix rule formula)
  , commandStackState :: (CommandStack ix rule formula)
  }

-- | Type contraints required to run the prover
--   using a given instantiation
type ProofConstraints ix rule formula error =
  ( Ord ix
  , ProofSystem error rule formula
  , Pretty ix
  , Pretty (rule ix)
  , Pretty formula
  )

-- | Monad that encorporates the actions and side effects characteristic of a
--   command-line proof assistant for Matching Logic
type MonadProver ix rule formula error m =
  ( ProofConstraints ix rule formula error
  , MonadRepl
    (ProverState ix rule formula)
    (ProverEnv ix rule formula error)
    m
  )

---------------
-- Main loop --
-- | prints initial prompt then calls the main Read-Eval-Print-Loop
--   upon termination, results in the final state of the proof and
--   command stack
runProver
  :: MonadProver ix rule formula error m
  => m (ProverState ix rule formula)
runProver = outputStrLn "Matching Logic prover started." >> repl >> get


-- | main loop:
--   parses command
--   if Ctrl-d (`Nothing`) exits prover
--   else if empty shows the proof in progress and the last command executed
--        if a valid prover command, applies it to the proof state
--        else prints parse error
--        loops
repl :: MonadProver ix rule formula error m => m ()
repl = do
    mStrCmd <- getInputLine ">>> "
    case mStrCmd of
        Nothing -> outputStrLn "Leaving Matching Logic prover..."
        Just ""     -> applyHelp >> repl
        Just strCmd -> do
          pCommand <- reader commandParser
          case parse pCommand "<stdin>" strCmd of
            Left  err -> outputStrLn (parseErrorPretty err) >> repl
            Right cmd' -> applyCommand cmd' >> repl



--------------------
-- Command monads --

-- | case split to handle the application of prover commands.
--   For each command there is a function that handles the
--   command that returns the new proof if successful, or Nothing
--   if it fails.
--   For commands that do not count as part of the
--   history of the proof (Undo, Show, Help), Nothing is always returned
--   TODO: clean this up
applyCommand
  :: MonadProver ix rule formula error m
  => Command ix rule formula
  -> m ()
applyCommand command = do
  mResult <- case command of
    Add ix f              -> applyAdd ix f
    AddAndProve ix f rule -> applyAddAndProve ix f rule
    Prove ix rule         -> applyProve ix rule
    Undo                  -> applyUndo >> return Nothing
    Show                  -> applyShow >> return Nothing
    Help                  -> applyHelp >> return Nothing
  case mResult of -- Did the command succeed?
    Nothing -> return () -- no
    Just proof -> do     -- yes, update state
      cmds <- gets commandStackState
      put ProverState{proofState = proof, commandStackState = command:cmds}

-- | add a derivation to the proof
applyProve
  :: MonadProver ix rule formula error m
  => ix -> rule ix
  -> m (Maybe (Proof ix rule formula))
applyProve ix rule = do
  proof <- gets proofState
  let eProof = Hilbert.derive proof ix rule
  eitherError2Maybe handleKoreError eProof

-- | add a claim to the proof
applyAdd
  :: MonadProver ix rule formula error m
  => ix -> formula
  -> m (Maybe (Proof ix rule formula))
applyAdd ix formula = do
  fVerifier <- reader formulaVerifier
  proof <- gets proofState
  let eProof = Hilbert.add fVerifier proof ix formula
  eitherError2Maybe handleKoreError eProof

-- | add a claim and it's derivation to the proof
applyAddAndProve
  :: MonadProver ix rule formula error m
  => ix -> formula -> rule ix
  -> m (Maybe (Proof ix rule formula))
applyAddAndProve ix f rule = do
    fVerifier <- reader formulaVerifier
    proof <- gets proofState
    let eProof = Hilbert.add fVerifier proof ix f
    mProof <- eitherError2Maybe handleKoreError eProof
    case mProof of
      Nothing -> return Nothing
      Just proof' ->
        eitherError2Maybe handleKoreError $ Hilbert.derive proof' ix rule

-- | display the proof and the last executed (effectual) command
applyShow :: MonadProver ix rule formula error m => m ()
applyShow = renderProof >> showPreviousCommand

-- | display the proof
renderProof :: MonadProver ix rule formula error m => m ()
renderProof = outputStrLn . show . Hilbert.renderProof =<< gets proofState

-- | peek the top of the command stack
showPreviousCommand :: MonadProver ix rule formula error m => m ()
showPreviousCommand = do
  cmds <- gets commandStackState
  when (not $ null cmds)
    ( do
        outputStrLn "Last Command:"
        outputStrLn $ '\t' : (show $ pretty $ head cmds)
    )

-- | show the helptext
applyHelp :: MonadProver ix rule formula error m => m ()
applyHelp = outputStrLn helpText

-- | helptext for te prover repl
--   TODO: Write this...
helpText :: String
helpText = "for more information view docs/prover_repl.md"

----------
-- Undo --
-- | case split for undo-ing the previous (effectual) prover command.
--   At this point, unless the command stack is empty, this
--   function always succeeds.
applyUndo
  :: MonadProver ix rule formula error m
  => m ()
applyUndo = do
  cmds <- gets commandStackState
  case cmds of
    [] -> outputStrLn "'Undo' failed, no previous command."
    Add         ix _  :_ -> modify $ undoAdd         ix
    Prove       ix _  :_ -> modify $ undoProve       ix
    AddAndProve ix _ _:_ -> modify $ undoAddAndProve ix
    _ -> error "Show, Help, Undo should not be added to command history"

-- | remove the previously added claim
undoAdd
  :: Ord ix => ix
  -> ProverState ix rule formula
  -> ProverState ix rule formula
undoAdd ix ProverState{proofState = proof, commandStackState = Add _ _:cmds} =
  ProverState
  { proofState =
      proof
      { index = Map.delete ix $ index proof
      , claims = (\ (claims' :|>  _) -> claims') (claims proof)
      , derivations = derivations proof
      }
  , commandStackState = cmds
  }
undoAdd _ _ = error "undoAdd: top of command stack is not an 'add ...'"

-- | remove the previously added derivation
undoProve
  :: Ord ix => ix
  -> ProverState ix rule formula
  -> ProverState ix rule formula
undoProve ix ProverState{proofState = proof, commandStackState = Prove _ _:cmds} =
  ProverState
  { proofState = proof { derivations = Map.delete ix $ derivations proof }
  , commandStackState = cmds
  }
undoProve _ _ = error "undoProve: top of command stack is not a 'prove ... by ...'"

-- | remove the previously added claim and derivation
undoAddAndProve
  :: Ord ix => ix
  -> ProverState ix rule formula
  -> ProverState ix rule formula
undoAddAndProve ix
  ProverState{ proofState = proof, commandStackState = AddAndProve _ _ _:cmds } =
  ProverState
  { proofState =
      proof
      { index = Map.delete ix $ index proof
      , claims = (\(claims' :|> _) -> claims') $ claims proof
      , derivations = Map.delete ix $ derivations proof
      }
  , commandStackState = cmds
  }
undoAddAndProve _ _ = error "undoAddAndProve: top of command stack is not an 'add ...  by ... '"

------------------
-- "exceptions" --
-- | converts an error to an IO action
eitherError2Maybe
  :: MonadProver ix rule formula mlError m
  => (error -> m ())
  -> Either error result
  -> m (Maybe result)
eitherError2Maybe handleError (Left  err) = handleError err >> return Nothing
eitherError2Maybe _           (Right res) = return $ Just res

-- | converts an error to an IO action
handleKoreError :: MonadProver ix rule formula error m =>  Error error -> m ()
handleKoreError err = outputStrLn $ "command failed " ++ printError err
