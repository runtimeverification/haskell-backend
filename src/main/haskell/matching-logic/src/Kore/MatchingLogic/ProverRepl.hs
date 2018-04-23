{-# LANGUAGE OverloadedStrings     #-}
{-|
Description: A simple textual interface for building a proof

A simple textual interface for building a proof, offering commands
directly corresponding to the 'Kore.MatchingLogic.HilbertProof' API.
Parsers must be provided for the formulas, rules, and labels of
a particular instance of 'HilbertProof'.
-}
module Kore.MatchingLogic.ProverRepl where
import           Control.Monad.State.Strict      (MonadState (..), execStateT)
import           Control.Monad.Trans             (MonadTrans (lift))
import           Data.Text                       (Text, pack)
import           Data.Text.Prettyprint.Doc       (Pretty (pretty), colon, (<+>))
import           Data.Void

import           Data.Text.Prettyprint.Doc       (Pretty (pretty), colon, (<+>))
import           System.Console.Haskeline
import           Text.Megaparsec
import           Text.Megaparsec.Char

import           Kore.MatchingLogic.HilbertProof
import           Data.Kore.Error

newtype ProverState ix rule formula =
  ProverState (Proof ix rule formula)

data Command id rule formula =
   Add id formula
 | Derive id formula (rule id)
 deriving Show

applyCommand :: (Ord id, Pretty id, ProofSystem error rule formula)
             => (formula -> Either (Error error) ())
             -> Command id rule formula
             -> Proof id rule formula
             -> Either (Error error) (Proof id rule formula)
applyCommand formulaVerifier command proof = case command of
  Add id f         -> add formulaVerifier proof id f
  Derive id f rule -> derive proof id f rule

type Parser = Parsec Void Text

parseCommand :: Parser id -> Parser formula -> Parser (rule id) -> Parser (Command id rule formula)
parseCommand pId pFormula pDerivation = do
  id <- pId
  space
  char ':'
  space
  formula <- pFormula
  space
  option (Add id formula)
    (do string "by"
        space
        rule <- pDerivation
        return (Derive id formula rule))

instance (Pretty id, Pretty formula, Pretty (rule id)) => Pretty (Command id rule formula) where
  pretty (Add id formula) = pretty id<+>colon<+>pretty formula
  pretty (Derive id formula rule) = pretty id<+>colon<+>pretty formula<+>pretty("by"::Text)<+>pretty rule

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
