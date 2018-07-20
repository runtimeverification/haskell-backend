{-# LANGUAGE OverloadedStrings #-}
import           Data.Char                                     (isAlphaNum)

import           Text.Megaparsec
import           Text.Megaparsec.Char
import           Data.Kore.AST.Common                   (SymbolOrAlias (..),
                                                         Variable)
import           Data.Kore.AST.MetaOrObject             (Meta (..))
import           Data.Kore.Parser.Parser
import           Kore.MatchingLogic.ProofSystem.MLProofSystem ()
import           Kore.MatchingLogic.HilbertProof
import           Kore.MatchingLogic.ProofSystem.Minimal
import           Kore.MatchingLogic.ProofSystem.Minimal.Syntax (parseMLRule)
import           Kore.MatchingLogic.ProverRepl

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

-- TODO: remove if not needed
-- testSignature :: SignatureInfo
-- testSignature = SignatureInfo
--   { sorts = Set.fromList ["Nat","Bool"]
--   , labels = Map.fromList [("plus",("Nat",["Nat","Nat"]))
--                           ,("succ",("Nat",["Nat"]))
--                           ,("zero",("Nat",[]))
--                           ]
--   }

main :: IO ()
main = proveCommand >> return ()