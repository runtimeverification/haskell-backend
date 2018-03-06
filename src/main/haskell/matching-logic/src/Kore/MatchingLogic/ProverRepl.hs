{-# LANGUAGE OverloadedStrings #-}
{-|
Description: A simple textual interface for building a proof

A simple textual interface for building a proof, offering commands
directly corresponding to the 'Kore.MatchingLogic.HilbertProof' API.
Parsers must be provided for the formulas, rules, and labels of
a particular instance of 'HilbertProof'.
-}
module Kore.MatchingLogic.ProverRepl where
import           Control.Monad.IO.Class          (liftIO)
import           Control.Monad.State.Strict      (MonadState (..), StateT,
                                                  execStateT, modify')
import           Control.Monad.Trans             (MonadTrans (lift))
import           Data.List                       (isPrefixOf, isSuffixOf)
import qualified Data.Map.Strict                 as Map
import           Data.Text                       (Text, pack)
import           Data.Void

import           Data.Text.Prettyprint.Doc       (Pretty (pretty), colon, (<+>))
import           System.Console.Haskeline
import           Text.Megaparsec
import           Text.Megaparsec.Char

import           Kore.MatchingLogic.HilbertProof

newtype ProverState ix rule formula =
  ProverState (Proof ix rule formula)

data Command id rule formula =
   Add id formula
 | Derive id formula (rule id)
 deriving Show

applyCommand :: (Ord id, ProofSystem rule formula)
             => Command id rule formula
             -> Proof id rule formula
             -> Maybe (Proof id rule formula)
applyCommand command proof = case command of
  Add id f         -> add proof id f
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

runProver :: (Ord ix, ProofSystem rule formula, Pretty ix, Pretty (rule ix), Pretty formula)
          => Parser (Command ix rule formula)
          -> ProverState ix rule formula
          -> IO (ProverState ix rule formula)
runProver pCommand initialState =
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
            case applyCommand cmd state of
              Just state' -> do
                lift (put (ProverState state'))
                outputStrLn (show (renderProof state'))
                repl
              Nothing -> outputStrLn "command failed" >> repl
        Nothing -> return ()
