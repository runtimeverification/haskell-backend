import Data.Char
       ( isAlphaNum )

import Text.Megaparsec
import Text.Megaparsec.Char

import Kore.AST.Common
       ( SymbolOrAlias (..), Variable )
import Kore.AST.MetaOrObject
       ( Meta (..) )
import Kore.MetaML.AST
       ( CommonMetaPattern )
import Kore.Parser.Parser
import Logic.Matching.Prover.Repl
import Logic.Matching.Rules.Kore ()
import Logic.Matching.Rules.Minimal
import Logic.Matching.Rules.Minimal.Syntax
       ( parseMLRule )
import Logic.Proof.Hilbert

-- TODO: still needed?
parseName :: Parser String
parseName = takeWhile1P Nothing isAlphaNum <* space

pCommand' :: Parser (Command String (MLRule (SymbolOrAlias Meta) (Variable Meta) CommonMetaPattern) CommonMetaPattern)
pCommand' = parseCommand parseName parseFormula parseRule
  where
    parseFormula = metaPatternParser
    parseRule    = parseMLRule metaSymbolOrAliasParser
                               metaVariableParser
                               parseFormula
                               parseName

proveCommand
    :: IO (ProverState
            String
            (MLRule (SymbolOrAlias Meta) (Variable Meta) CommonMetaPattern)
            CommonMetaPattern)
proveCommand = runProver dummyFormulaVerifier pCommand' (ProverState emptyProof)

main :: IO ()
main = proveCommand >> return ()
