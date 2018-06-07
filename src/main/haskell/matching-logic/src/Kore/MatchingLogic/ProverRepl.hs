{-# LANGUAGE OverloadedStrings     #-}
{-|
Description: A simple textual interface for building a proof

A simple textual interface for building a proof, offering commands
directly corresponding to the 'Kore.MatchingLogic.HilbertProof' API.
Parsers must be provided for the formulas, rules, and labels of
a particular instance of 'HilbertProof'.
-}
module Kore.MatchingLogic.ProverRepl where
import           Control.Monad.State.Strict      (MonadState (get,put), execStateT)
import           Control.Monad.Trans             (MonadTrans (lift))
import           Data.Text                       (Text, pack)
import           Data.Void

import           Data.Text.Prettyprint.Doc       (Pretty (pretty), colon, (<+>))
import           System.Console.Haskeline
import           Text.Megaparsec
import           Text.Megaparsec.Char

import           Kore.MatchingLogic.HilbertProof
import           Data.Kore.Error

newtype ProverState ix rule formula =
  ProverState (Proof ix rule formula)

data Command ix rule formula =
   Add ix formula
 | Derive ix formula (rule ix)
 deriving Show

applyCommand :: (Ord ix, Pretty ix, ProofSystem error rule formula)
             => (formula -> Either (Error error) ())
             -> Command ix rule formula
             -> Proof ix rule formula
             -> Either (Error error) (Proof ix rule formula)
applyCommand formulaVerifier command proof = case command of
  Add ix f         -> add formulaVerifier proof ix f
  Derive ix f rule -> derive proof ix f rule

type Parser = Parsec Void Text

parseCommand :: Parser ix -> Parser formula -> Parser (rule ix) -> Parser (Command ix rule formula)
parseCommand pIx pFormula pDerivation = do
  ix <- pIx
  space >> char ':' >> space
  formula <- pFormula
  space
  option
    (Add ix formula)
    (Derive ix formula <$ string "by" <* space <*> pDerivation)

instance (Pretty ix, Pretty formula, Pretty (rule ix)) => Pretty (Command ix rule formula) where
  pretty (Add ix formula) = pretty ix<+>colon<+>pretty formula
  pretty (Derive ix formula rule) = pretty ix<+>colon<+>pretty formula<+>pretty("by"::Text)<+>pretty rule

runProver
  ::  ( Ord ix
      , ProofSystem error rule formula
      , Pretty ix
      , Pretty (rule ix)
      , Pretty formula)
  => (formula -> Either (Error error) ())
  -> Parser (Command ix rule formula)
  -> ProverState ix rule formula
  -> IO (ProverState ix rule formula)
runProver formulaVerifier pCommand initialState =
    execStateT (runInputT defaultSettings startRepl) initialState
  where
    startRepl = outputStrLn "Matching Logic prover started" >> repl
    repl = do
      mcommand <- getInputLine ">>> "
      case mcommand of
        Just "" -> do ProverState state <- lift get
                      outputStrLn (show (renderProof state))
                      repl
        Just command -> case parse pCommand "<stdin>" (pack command) of
          Left err -> outputStrLn (parseErrorPretty err) >> repl
          Right cmd -> do
            ProverState state <- lift get
            case applyCommand formulaVerifier cmd state of
              Right state' -> do
                lift (put (ProverState state'))
                outputStrLn (show (renderProof state'))
                repl
              Left err ->
                outputStrLn ("command failed" ++ printError err) >> repl
        Nothing -> return ()
