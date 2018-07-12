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
import           Data.Map.Strict                 (Map)
import qualified Data.Map.Strict                 as Map

import           Data.Text.Prettyprint.Doc       (Pretty (pretty), colon, (<+>))
import           System.Console.Haskeline
import           Text.Megaparsec
import           Text.Megaparsec.Char

import           Kore.MatchingLogic.HilbertProof
import           Data.Kore.Error
import           Kore.MatchingLogic.Error

newtype ProverState ix rule formula =
  ProverState (Proof ix rule formula)

data Command ix rule formula =
   Add ix formula
 | Prove ix (rule ix)
 | AddAndProve ix formula (rule ix)
 deriving Show

applyAddAndProve :: (Ord ix, Pretty ix, ProofSystem error rule formula)
                 => (formula -> Either (Error error) ())
                 -> Proof ix rule formula
                 -> ix -> formula -> (rule ix)
                 -> Either (Error error) (Proof ix rule formula)
applyAddAndProve formulaVerifier proof ix f rule = 
  do 
    proof' <- add formulaVerifier proof ix f
    derive proof' ix f rule 

applyProve :: (Ord ix, Pretty ix, ProofSystem error rule formula)
           => Proof ix rule formula
           -> ix -> (rule ix)
           -> Either (Error error) (Proof ix rule formula)
applyProve proof ix rule = do
  f' <- case Map.lookup ix (index proof) of
          Nothing    ->   mlFail ["Formula with ID ", pretty ix, "not found"]
          Just (_,f) -> return f
  derive proof ix f' rule 

applyAdd :: (Ord ix, Pretty ix, ProofSystem error rule formula)
         => (formula -> Either (Error error) ())
         -> Proof ix rule formula
         -> ix -> formula
         -> Either (Error error) (Proof ix rule formula)
applyAdd = add

applyCommand :: (Ord ix, Pretty ix, ProofSystem error rule formula)
             => (formula -> Either (Error error) ())
             -> Command ix rule formula
             -> Proof ix rule formula
             -> Either (Error error) (Proof ix rule formula)
applyCommand formulaVerifier command proof = case command of
  Add ix f              -> applyAdd formulaVerifier proof ix f
  AddAndProve ix f rule -> applyAddAndProve formulaVerifier proof ix f rule
  Prove ix rule         -> applyProve proof ix rule

type Parser = Parsec Void Text

parseAdd :: Parser ix -> Parser formula -> Parser (rule ix) -> Parser (Command ix rule formula)
parseAdd pIx pFormula pDerivation = do
  string "add"
  space
  ix <- pIx
  space >> char ':' >> space
  formula <- pFormula
  space
  option
    (Add ix formula)
    (AddAndProve ix formula <$ string "by" <* space <*> pDerivation)

parseDeriveRef :: Parser ix -> Parser formula -> Parser (rule ix) -> Parser (Command ix rule formula)
parseDeriveRef pIx pFormula pDerivation = do
  string "prove"
  space
  ix <- pIx
  space
  string "by"
  space
  rule <- pDerivation
  return (Prove ix rule)

parseCommand :: Parser ix -> Parser formula -> Parser (rule ix) -> Parser (Command ix rule formula)
parseCommand pIx pFormula pDerivation 
  =  parseDeriveRef pIx pFormula pDerivation
 <|> parseAdd pIx pFormula pDerivation

instance (Pretty ix, Pretty formula, Pretty (rule ix)) => Pretty (Command ix rule formula) where
  pretty (Add ix formula)              = pretty("add"::Text)<+>pretty ix<+>colon<+>pretty formula
  pretty (Prove ix rule)               = pretty("prove"::Text)<+>pretty ix<+>colon<+>pretty("by"::Text)<+>pretty rule
  pretty (AddAndProve ix formula rule) = pretty("add"::Text)<+>pretty ix<+>colon<+>pretty formula<+>pretty("by"::Text)<+>pretty rule

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
