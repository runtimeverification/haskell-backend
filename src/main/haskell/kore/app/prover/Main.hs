import           Data.Char                                     (isAlphaNum)
import qualified Data.Map.Strict                               as Map
import qualified Data.Set                                      as Set
import           Data.Text

import           Text.Megaparsec
import           Text.Megaparsec.Char

import           Data.Reflection

import           Logic.Matching.Pattern
import           Kore.MatchingLogic.AST.Syntax
import           Kore.MatchingLogic.HilbertProof
import           Kore.MatchingLogic.ProofSystem.Minimal
import           Kore.MatchingLogic.ProofSystem.Minimal.Syntax (parseMLRuleSig)
import           Kore.MatchingLogic.ProverRepl
import           Kore.MatchingLogic.Signature.Simple

-- Todo: Parsing Formula as Text. Hook to Kore Parser
parseName :: Parser Text
parseName = takeWhile1P Nothing isAlphaNum <* space

pCommand :: (Reifies s ValidatedSignature)
         => Parser (Command Text
                    (MLRuleSig (SimpleSignature s) Text)
                    (WFPattern (SimpleSignature s) Text))
pCommand = parseCommand parseName parseFormula parseRule
  where
    parseFormula = simpleSigPattern parseName parseName parseName
    parseLabel = simpleSigLabel parseName
    parseSort = simpleSigSort parseName
    parseRule = parseMLRuleSig parseSort parseLabel parseName parseName

proveCommand
    :: (Reifies sig ValidatedSignature)
    => proxy (SimpleSignature sig)
    -> IO (ProverState Text (MLRuleSig (SimpleSignature sig) Text)
            (WFPattern (SimpleSignature sig) Text))
proveCommand _ = runProver dummyFormulaVerifier pCommand (ProverState emptyProof)

testSignature :: SignatureInfo
testSignature = SignatureInfo
  { sorts = Set.fromList ["Nat","Bool"]
  , labels = Map.fromList [("plus",("Nat",["Nat","Nat"]))
                          ,("succ",("Nat",["Nat"]))
                          ,("zero",("Nat",[]))
                          ]
  }

main :: IO ()
main = case validate testSignature of
  Nothing -> return ()
  Just validSig -> reifySignature validSig (\proxy -> proveCommand proxy >> return ())
