{-# LANGUAGE OverloadedStrings #-}
import           Data.Char                                     (isAlphaNum)
import qualified Data.Map.Strict                               as Map
import qualified Data.Set                                      as Set
import           Data.Text

import           Text.Megaparsec
import           Text.Megaparsec.Char
import           Data.Text.Prettyprint.Doc                     (Pretty (..))

import           Data.Reflection

import           Data.Kore.AST.Common                   (SymbolOrAlias (..),
                                                         Variable)
import           Data.Kore.AST.MetaOrObject             (Meta (..),
                                                         Unified (..))
import           Data.Kore.Parser.Parser
import           Kore.MatchingLogic.AST
import           Kore.MatchingLogic.AST.Syntax
import           Kore.MatchingLogic.ProofSystem.MLProofSystem
import           Kore.MatchingLogic.HilbertProof
import           Kore.MatchingLogic.ProofSystem.Minimal
import           Kore.MatchingLogic.ProofSystem.Minimal.Syntax (parseMLRuleSig, parseMLRule)
import           Kore.MatchingLogic.ProverRepl
import           Kore.MatchingLogic.Signature.Simple

-- Todo: Parsing Formula as Text. Hook to Kore Parser
parseName :: Parser String
parseName = takeWhile1P Nothing isAlphaNum <* space

-- pCommand :: (Reifies s ValidatedSignature)
--          => Parser (Command String
--                     (MLRuleSig (SimpleSignature s) String)
--                     (WFPattern (SimpleSignature s) String))
-- pCommand = parseCommand parseName parseFormula parseRule
--   where
--     parseFormula = simpleSigPattern parseName parseName parseName
--     parseLabel = simpleSigLabel parseName
--     parseSort = simpleSigSort parseName
--     parseRule = parseMLRuleSig parseSort parseLabel parseName parseName

pCommand' :: Parser (Command String (MLRule (SymbolOrAlias Meta) (Variable Meta) CommonMetaPattern) CommonMetaPattern)
pCommand' = parseCommand parseName parseFormula parseRule
  where
    parseFormula = metaPatternParser
    parseLabel = parseName
    parseSort = parseName
    x = metaSymbolOrAliasParser
    y = metaVariableParser
    parseRule = parseMLRule x y parseFormula parseName  

instance Pretty (SymbolOrAlias t) where
    pretty _ = pretty "SymbolOrAlias"

instance Pretty (Variable t) where
    pretty _ = pretty "Variable"

-- proveCommand
--     :: (Reifies sig ValidatedSignature)
--     => proxy (SimpleSignature sig)
--     -> IO (ProverState Text (MLRuleSig (SimpleSignature sig) Text)
--             (WFPattern (SimpleSignature sig) Text))
proveCommand
    :: IO (ProverState 
            String 
            (MLRule (SymbolOrAlias Meta) (Variable Meta) CommonMetaPattern)
            CommonMetaPattern)
proveCommand = runProver dummyFormulaVerifier pCommand' (ProverState emptyProof)


testSignature :: SignatureInfo
testSignature = SignatureInfo
  { sorts = Set.fromList ["Nat","Bool"]
  , labels = Map.fromList [("plus",("Nat",["Nat","Nat"]))
                          ,("succ",("Nat",["Nat"]))
                          ,("zero",("Nat",[]))
                          ]
  }

-- main :: IO ()
-- main = case validate testSignature of
--   Nothing -> return ()
--   Just validSig -> reifySignature validSig (\proxy -> proveCommand proxy >> return ())

main :: IO ()
main = proveCommand >> return ()