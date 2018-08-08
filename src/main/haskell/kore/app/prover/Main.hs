import Data.Char
       ( isAlphaNum )
import Text.Megaparsec
import Text.Megaparsec.Char

import Kore.MetaML.AST
       ( CommonMetaPattern )
import Kore.Parser.Parser
       ( metaHeadParser, metaPatternParser, metaVariableParser )

import qualified Logic.Matching.Rules.Kore as ML
                 ( Rule )
import           Logic.Matching.Rules.Minimal
import           Logic.Matching.Rules.Minimal.Syntax
                 ( parseMLRule )
import           Logic.Proof.Hilbert
                 ( emptyProof )

import Logic.Matching.Prover.Command
       ( Command, Parser, parseCommand )
import Logic.Matching.Prover.Repl
       ( ProverEnv (..), ProverState (..), defaultSettings, execReplT,
       runProver )

import GlobalMain
       ( defaultMainGlobal )

-- TODO: still needed?
parseName :: Parser String
parseName = takeWhile1P Nothing isAlphaNum <* space

pCommand :: Parser (Command String ML.Rule CommonMetaPattern)
pCommand = parseCommand parseName parseFormula parseRule
  where
    parseFormula = metaPatternParser
    parseRule    = parseMLRule metaHeadParser
                               metaVariableParser
                               parseFormula
                               parseName

main :: IO ()
main = defaultMainGlobal
       >> execReplT runProver defaultSettings proverEnv initialState
       >> return ()
  where
    initialState = ProverState
                   { proofState = emptyProof
                   , commandStackState = []
                   }
    proverEnv    = ProverEnv
                   { commandParser = pCommand
                   , formulaVerifier = dummyFormulaVerifier
                   }
