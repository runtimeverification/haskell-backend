{-|
Description: A simple textual interface for building a proof

A simple textual interface for building a proof, offering commands
directly corresponding to the 'Kore.MatchingLogic.HilbertProof' API.
Parsers must be provided for the formulas, rules, and labels of
a particular instance of 'HilbertProof'.
-}
module Logic.Matching.Prover.Repl
  ( ProverState(..)
  , ProverEnv(..)
  , runProver
  , execReplT
  , defaultSettings )
where

import Control.Monad.State.Strict
       (get, gets, put, modify)
import Control.Monad.Reader (reader)
import Control.Monad (when)

import qualified Data.Map.Strict as Map
import Data.Sequence (Seq((:|>)))

import Data.Text.Prettyprint.Doc
       ( Pretty (pretty))
import Text.Megaparsec
       (parse, parseErrorPretty)

import Kore.Parser.ParserUtils ()
import Kore.Error

import           Logic.Proof.Hilbert
                 (ProofSystem(..), Proof(..))
import qualified Logic.Proof.Hilbert as Hilbert
import           Logic.Matching.Prover.Repl.Class
                 (MonadRepl, MonadHaskeline(..), execReplT, defaultSettings)
import           Logic.Matching.Prover.Command
                 (Command(..), Parser)


type CommandStack ix rule formula = [Command ix rule formula]

data ProverEnv ix rule formula error =
  ProverEnv
  { commandParser   :: !(Parser (Command ix rule formula))
  , formulaVerifier :: !(formula -> Either (Error error) ())
  }

data ProverState ix rule formula =
  ProverState
  { proofState :: (Proof ix rule formula)
  , commandStackState :: (CommandStack ix rule formula)
  }

type ProofConstraints ix rule formula error =
  ( Ord ix
  , ProofSystem error rule formula
  , Pretty ix
  , Pretty (rule ix)
  , Pretty formula
  )

type MonadProver ix rule formula error m =
  ( ProofConstraints ix rule formula error
  , MonadRepl
    (ProverState ix rule formula)
    (ProverEnv ix rule formula error)
    m
  )

---------------
-- Main loop --
runProver
  :: MonadProver ix rule formula error m
  => m (ProverState ix rule formula)
runProver = outputStrLn "Matching Logic prover started." >> repl >> get

repl :: MonadProver ix rule formula error m => m ()
repl =
    getInputLine ">>> " >>= \case
        Nothing -> outputStrLn "Leaving Matching Logic prover..."
        Just ""     -> applyHelp >> repl
        Just strCmd -> do
          pCommand <- reader commandParser
          case parse pCommand "<stdin>" strCmd of
            Left  err -> outputStrLn (parseErrorPretty err) >> repl
            Right cmd' -> applyCommand cmd' >> repl
            


--------------------
-- Command monads --
applyCommand
  :: MonadProver ix rule formula error m
  => Command ix rule formula
  -> m ()
applyCommand command = do
  case command of
    Add ix f              -> applyAdd ix f
    AddAndProve ix f rule -> applyAddAndProve ix f rule
    Prove ix rule         -> applyProve ix rule
    Undo                  -> applyUndo >> return Nothing -- not added to command stack
    Show                  -> applyShow >> return Nothing -- same
    Help                  -> applyHelp >> return Nothing 
  >>= \case  -- Did the command succeed?
    Nothing -> return () -- no
    Just proof -> do     -- yes, update state
      cmds <- gets commandStackState
      put ProverState{proofState = proof, commandStackState = command:cmds}

applyProve
  :: MonadProver ix rule formula error m
  => ix -> rule ix
  -> m (Maybe (Proof ix rule formula))
applyProve ix rule = do
  proof <- gets proofState
  let eProof = Hilbert.derive proof ix rule
  eitherError2Maybe handleKoreError eProof

applyAdd 
  :: MonadProver ix rule formula error m
  => ix -> formula
  -> m (Maybe (Proof ix rule formula))
applyAdd ix formula = do
  fVerifier <- reader formulaVerifier
  proof <- gets proofState
  let eProof = Hilbert.add fVerifier proof ix formula
  eitherError2Maybe handleKoreError eProof

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

applyShow :: MonadProver ix rule formula error m => m ()
applyShow = renderProof >> showPreviousCommand

renderProof :: MonadProver ix rule formula error m => m ()
renderProof = outputStrLn . show . Hilbert.renderProof =<< gets proofState

showPreviousCommand :: MonadProver ix rule formula error m => m ()
showPreviousCommand = do
  cmds <- gets commandStackState
  when (not $ null cmds)
    ( do
        outputStrLn "Last Command:"
        outputStrLn $ '\t' : (show $ pretty $ head cmds)
    )

applyHelp :: MonadProver ix rule formula error m => m ()
applyHelp = outputStrLn helpText

helpText :: String
helpText = "for more information view prover_repl.md"
----------
-- Undo --
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

-- "exceptions"
eitherError2Maybe
  :: MonadProver ix rule formula mlError m
  => (error -> m ())
  -> Either error result
  -> m (Maybe result)
eitherError2Maybe handleError =
  \case
    Left err -> handleError err >> return Nothing
    Right result -> return $ Just result

handleKoreError :: MonadProver ix rule formula error m =>  Error error -> m ()
handleKoreError err = outputStrLn $ "command failed " ++ printError err
