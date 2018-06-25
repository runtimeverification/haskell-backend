{-# LANGUAGE FlexibleInstances #-}
module TestUtils where

import           Control.Applicative                           (some)
import           Data.Text                                     (Text)
import qualified Data.Text                                     as T
import           Data.Void
import           Text.Megaparsec                               hiding (some)
import           Text.Megaparsec.Char

import           Kore.MatchingLogic.ProofSystem.Minimal
import           Kore.MatchingLogic.ProofSystem.Minimal.Syntax



type DummyParser = Parsec Void Text

type DummySort  = Text
type DummyLabel = Text
type DummyIx    = Int
type DummyVar   = Text
type DummyTerm  = Text

sortParser       :: DummyParser DummySort
labelParser      :: DummyParser DummyLabel
ixParser         :: DummyParser DummyIx
varParser        :: DummyParser DummyVar
termParser       :: DummyParser DummyTerm
mlRuleTestParser :: DummyParser (MLRule DummyLabel DummyVar DummyTerm DummyIx)

-- Implementations for Dummy Parsers, shared by tests
sortParser       = T.pack <$> some alphaNumChar
labelParser      = T.pack <$> some alphaNumChar
ixParser         = read   <$> some digitChar
varParser        = T.pack <$> some alphaNumChar
termParser       = T.pack <$> some alphaNumChar
mlRuleTestParser = parseMLRule labelParser varParser mlPatternParser ixParser


testPatterns :: [String]
testPatterns = [  "P"
                , "Q"
                , "R" ]

mlTestPatterns :: [DummyParser DummyTerm]
mlTestPatterns = string <$> T.pack <$> testPatterns

mlPatternParser :: DummyParser DummyTerm
mlPatternParser = choice mlTestPatterns


-- Dummy Rule Type instantiated with Dummy Parsers
type DummyRule = MLRule DummyLabel DummyVar DummyTerm DummyIx

parseTestRule :: String -> DummyRule

parseTestRule ruleStr = case (parse mlRuleTestParser "" (T.pack ruleStr)) of
                          Right parsedRule -> parsedRule
                          Left err -> error (parseErrorPretty err)


prop1RuleStr :: String
prop1RuleStr = "propositional1(P, Q)"

               
               
prop1RuleAST :: DummyRule
prop1RuleAST =  Propositional1 (T.pack "P") (T.pack "Q")


prop2RuleStr :: String
prop2RuleStr = "propositional2(P, Q, R)"

prop2RuleAST :: DummyRule
prop2RuleAST =  Propositional2 (T.pack "P") (T.pack "Q") (T.pack "R")


prop3RuleStr :: String
prop3RuleStr = "propositional3(P, Q)"

prop3RuleAST :: DummyRule
prop3RuleAST =  Propositional3 (T.pack "P") (T.pack "Q")

mpRuleStr :: String
mpRuleStr = "mp(1, 2)"

mpRuleAST :: DummyRule
mpRuleAST = ModusPonens 1 2

ugRuleStr :: String
ugRuleStr = "ug(x, 1)"

ugRuleAST :: DummyRule
ugRuleAST = Generalization (T.pack "x") 1

varSubstStr :: String
varSubstStr = "varsubst(x, P, y)"

varSubstAST :: DummyRule
varSubstAST = VariableSubstitution (SubstitutedVariable (T.pack "x")) (T.pack "P") (SubstitutingVariable (T.pack "y"))

forAllStr :: String
forAllStr = "forall(x, P, Q)"

forAllAST :: DummyRule
forAllAST = ForallRule (T.pack "x") (T.pack "P") (T.pack "Q")

framingStr :: String
framingStr = "framing(x, 2, 1)"

framingAST :: DummyRule
framingAST = Framing (T.pack "x") 2 1


propagateOrStr :: String
propagateOrStr = "propagate-or(sigma, 2, P, Q)"

propagateOrAST :: DummyRule
propagateOrAST = PropagateOr (T.pack "sigma") 2 (T.pack "P") (T.pack "Q")

propagateExistsStr :: String
propagateExistsStr = "propagate-exists(sigma, 2, x, P)"

propagateExistsAST :: DummyRule
propagateExistsAST = PropagateExists (T.pack "sigma") 2 (T.pack "x") (T.pack "P")

existsStr :: String
existsStr = "exists(x)"

existsAST :: DummyRule
existsAST = Existence (T.pack "x")

singvarStr :: String
singvarStr = "singvar(x, P, 1, 1)"

singvarAST :: DummyRule
singvarAST = Singvar (T.pack "x") (T.pack "P") [1] [1]
