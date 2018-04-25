module RuleParserTests(ruleParsingTests, ruleUnparsingTests) where

import           Control.Applicative                           (some)
import           Data.Text                                     (Text)
import qualified Data.Text                                     as T
import           Data.Void

import           Test.Tasty                                    (TestTree,
                                                                testGroup)
import           Test.Tasty.HUnit

import           Data.Text.Prettyprint.Doc
import           Text.Megaparsec                               hiding (some)
import           Text.Megaparsec.Char

import           Kore.MatchingLogic.AST
import           Kore.MatchingLogic.HilbertProof
import           Kore.MatchingLogic.ProofSystem.Minimal
import           Kore.MatchingLogic.ProofSystem.Minimal.Syntax
import           TestUtils


{-
 - Rule Parsing Unit Tests
-}

ruleParsingTests =
      testGroup
        "Rule Parser Unit Tests"
        [  prop1Test
          ,prop2Test
          ,prop3Test
          ,mpTest
          ,ugTest
          ,varSubstTest
          ,forAllTest
          ,framingTest
          ,propagateOrTest
          ,propagateExistsTest
          ,existsTest
          ,singvarTest
        ]


prop1Test           = testCase
                        ("Propositional1")
                         (assertEqual " Propositional1" prop1RuleAST (parseTestRule prop1RuleStr))


prop2Test           = testCase
                        ("Propositional2")
                          (assertEqual " Propositional2" prop2RuleAST (parseTestRule prop2RuleStr))



prop3Test           = testCase
                        ("Propositional3")
                          (assertEqual " Propositional3 Failure" prop3RuleAST (parseTestRule prop3RuleStr))

mpTest              = testCase
                        ("ModusPonens")
                          (assertEqual " Modus Ponens" mpRuleAST (parseTestRule mpRuleStr))


ugTest              = testCase
                        ("Universal Generalization")
                          (assertEqual " Universal Generalization" ugRuleAST (parseTestRule ugRuleStr))


varSubstTest        = testCase
                        ("Variable Substitution")
                          (assertEqual " Variable Substitution" varSubstAST (parseTestRule varSubstStr))



forAllTest          = testCase
                        ("ForAll")
                          (assertEqual " ForAll" forAllAST (parseTestRule forAllStr))


framingTest   = testCase
                        ("Framing")
                          (assertEqual " Framing" framingAST (parseTestRule framingStr))


propagateOrTest     = testCase
                        ("PropagateOr")
                          (assertEqual " PropagateOr" propagateOrAST (parseTestRule propagateOrStr))


propagateExistsTest = testCase
                        ("PropagateExists")
                          (assertEqual " PropagateExists" propagateExistsAST (parseTestRule propagateExistsStr))


existsTest          = testCase
                        ("Existence")
                          (assertEqual " Existence" existsAST (parseTestRule existsStr))

singvarTest         = testCase
                        ("SingVar")
                          (assertEqual " Singvar" singvarAST (parseTestRule singvarStr))


{-
 Rule Unparser Unit Tests
 -}

ruleUnparsingTests =
      testGroup
        "Rule Unparser Unit Tests"
        [  prop1UnparsingTest
          ,prop2UnparsingTest
          ,prop3UnparsingTest
          ,mpUnparsingTest
          ,ugUnparsingTest
          ,varSubstUnparsingTest
          ,forAllUnparsingTest
          ,framingUnparsingTest
          ,propagateOrUnparsingTest
          ,propagateExistsUnparsingTest
          ,existsUnparsingTest
          ,singvarUnparsingTest
                              ]
-- Prop1 Unparsing Test

prop1UnparsingTest           = testCase
                                ("Propositional1 Unparsing")
                                   (assertEqual " Propositional1 Unparsing" prop1RuleStr
                                      (show $ pretty prop1RuleAST))

prop2UnparsingTest           = testCase
                                ("Propositional2 Unparsing")
                                  (assertEqual " Propositional2 Unparsing" prop2RuleStr
                                      (show $ pretty prop2RuleAST))

prop3UnparsingTest           = testCase
                                ("Propositional3 Unparsing")
                                  (assertEqual " Propositional3 Unparsing" prop3RuleStr
                                    (show $ pretty prop3RuleAST))

mpUnparsingTest              = testCase
                                ("MP Unparsing")
                                  (assertEqual " Propositional3 Unparsing" mpRuleStr
                                    (show $ pretty mpRuleAST))

ugUnparsingTest              = testCase
                                ("Universal Generalization Unparsing")
                                  (assertEqual " Universal Generalization Unparsing" ugRuleStr
                                    (show $ pretty ugRuleAST))

varSubstUnparsingTest        = testCase
                                ("Variable Substitution Unparsing")
                                  (assertEqual " Variable Substitution Unparsing" varSubstStr
                                    (show $ pretty varSubstAST))

forAllUnparsingTest          = testCase
                                ("Forall Unparsing")
                                  (assertEqual " Forall Unparsing" forAllStr
                                    (show $ pretty forAllAST))

framingUnparsingTest   = testCase
                                ("Framing Unparsing")
                                  (assertEqual " Framing Unparsing" framingStr
                                    (show $ pretty framingAST))

propagateExistsUnparsingTest = testCase
                                ("Propagate Exists Unparsing")
                                 (assertEqual " PropagateExists Unparsing" propagateExistsStr
                                  (show $ pretty propagateExistsAST))

propagateOrUnparsingTest     = testCase
                                ("Propagate Or Unparsing")
                                  (assertEqual " Propagate Or Unparsing" propagateOrStr
                                    (show $ pretty propagateOrAST))

existsUnparsingTest          = testCase
                                ("Exists Unparsing")
                                 (assertEqual " Exists Unparsing" existsStr
                                  (show $ pretty existsAST))

singvarUnparsingTest         = testCase
                                ("Singvar Unparsing")
                                  (assertEqual " Singvar Unparsing" singvarStr
                                    (show $ pretty singvarAST))


