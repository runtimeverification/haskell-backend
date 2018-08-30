module Test.Logic.Matching.Rules.Minimal where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit

import Control.Applicative
       ( some )
import Data.Text.Prettyprint.Doc
import Text.Megaparsec hiding
       ( some )
import Text.Megaparsec.Char

import Kore.Parser.ParserUtils ()
import Logic.Matching.Rules.Minimal
import Logic.Matching.Rules.Minimal.Syntax

test :: String -> DummyRule -> String -> TestTree
test name ast str =
  testGroup name
  [ testCase "Parse" (ast @=? parseTestRule str)
  , testCase "Unparse" (str @=? show (pretty ast))
  ]

test_prop1 :: TestTree
test_prop1 = test "Propositional 1" ast str
  where
    ast = Propositional1 "P" "Q"
    str = "propositional1(P, Q)"

test_prop2 :: TestTree
test_prop2 = test "Propositional 2" ast str
  where
    ast = Propositional2 "P" "Q" "R"
    str = "propositional2(P, Q, R)"


test_prop3 :: TestTree
test_prop3 = test "Propositional 3" ast str
  where
    ast = Propositional3 "P" "Q"
    str = "propositional3(P, Q)"

test_modusPonens :: TestTree
test_modusPonens = test "Modus Ponens" ast str
  where
    ast = ModusPonens 1 2
    str = "mp(1, 2)"

test_universalGeneralization :: TestTree
test_universalGeneralization = test "Universal Generalization" ast str
  where
    ast = Generalization "x" 1
    str = "ug(x, 1)"

test_variableSubstitution :: TestTree
test_variableSubstitution = test "Variable Substitution" ast str
  where
    ast = VariableSubstitution (SubstitutedVariable "x") "P" (SubstitutingVariable "y")
    str = "varsubst(x, P, y)"

test_forall :: TestTree
test_forall = test "Forall" ast str
  where
    ast = ForallRule "x" "P" "Q"
    str = "forall(x, P, Q)"

test_framing :: TestTree
test_framing = test "Framing" ast str
  where
    ast = Framing "x" 2 1
    str = "framing(x, 2, 1)"

test_propagateOr :: TestTree
test_propagateOr = test "Propagate Or" ast str
  where
    ast = PropagateOr "sigma" 2 "P" "Q"
    str = "propagate-or(sigma, 2, P, Q)"

test_propagateExists :: TestTree
test_propagateExists = test "Propagate Exists" ast str
  where
    ast = PropagateExists "sigma" 2 "x" "P"
    str = "propagate-exists(sigma, 2, x, P)"

test_exists :: TestTree
test_exists = test "Existence" ast str
  where
    ast = Existence "x"
    str = "exists(x)"

test_singularVariable :: TestTree
test_singularVariable = test "Singular Variable" ast str
  where
    ast = Singvar "x" "P" [1] [1]
    str = "singvar(x, P, 1, 1)"


type DummyParser = Parsec String String

type DummySort  = String
type DummyLabel = String
type DummyIx    = Int
type DummyVar   = String
type DummyTerm  = String

sortParser       :: DummyParser DummySort
labelParser      :: DummyParser DummyLabel
ixParser         :: DummyParser DummyIx
varParser        :: DummyParser DummyVar
termParser       :: DummyParser DummyTerm
mlRuleTestParser :: DummyParser (MLRule DummyLabel DummyVar DummyTerm DummyIx)

sortParser       = some alphaNumChar
labelParser      = some alphaNumChar
ixParser         = read   <$> some digitChar
varParser        = some alphaNumChar
termParser       = some alphaNumChar
mlRuleTestParser = parseMLRule labelParser varParser mlPatternParser ixParser

testPatterns :: [String]
testPatterns = [  "P"
                , "Q"
                , "R" ]

mlTestPatterns :: [DummyParser DummyTerm]
mlTestPatterns = string <$> testPatterns

mlPatternParser :: DummyParser DummyTerm
mlPatternParser = choice mlTestPatterns


-- Dummy Rule Type instantiated with Dummy Parsers
type DummyRule = MLRule DummyLabel DummyVar DummyTerm DummyIx

parseTestRule :: String -> DummyRule

parseTestRule ruleStr =
    case parse mlRuleTestParser "" ruleStr of
        Right parsedRule -> parsedRule
        Left err -> error (parseErrorPretty err)
