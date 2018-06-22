module RuleParserTests(ruleParsingTests, ruleUnparsingTests) where

import           Test.Tasty                                    (TestTree,
                                                                testGroup)
import           Test.Tasty.HUnit

import           Data.Text.Prettyprint.Doc
import           TestUtils


{-
 - Rule Parsing Unit Tests
-}
ruleParsingTests :: TestTree
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

prop1Test :: TestTree
prop1Test           = testCase
                        ("Propositional1")
                         (assertEqual " Propositional1" prop1RuleAST (parseTestRule prop1RuleStr))
prop2Test :: TestTree
prop2Test           = testCase
                        ("Propositional2")
                          (assertEqual " Propositional2" prop2RuleAST (parseTestRule prop2RuleStr))


prop3Test :: TestTree
prop3Test           = testCase
                        ("Propositional3")
                          (assertEqual " Propositional3 Failure" prop3RuleAST (parseTestRule prop3RuleStr))
mpTest :: TestTree
mpTest              = testCase
                        ("ModusPonens")
                          (assertEqual " Modus Ponens" mpRuleAST (parseTestRule mpRuleStr))

ugTest :: TestTree
ugTest              = testCase
                        ("Universal Generalization")
                          (assertEqual " Universal Generalization" ugRuleAST (parseTestRule ugRuleStr))

varSubstTest :: TestTree
varSubstTest        = testCase
                        ("Variable Substitution")
                          (assertEqual " Variable Substitution" varSubstAST (parseTestRule varSubstStr))


forAllTest :: TestTree
forAllTest          = testCase
                        ("ForAll")
                          (assertEqual " ForAll" forAllAST (parseTestRule forAllStr))

framingTest :: TestTree
framingTest         = testCase
                        ("Framing")
                          (assertEqual " Framing" framingAST (parseTestRule framingStr))

propagateOrTest :: TestTree
propagateOrTest     = testCase
                        ("PropagateOr")
                          (assertEqual " PropagateOr" propagateOrAST (parseTestRule propagateOrStr))

propagateExistsTest :: TestTree
propagateExistsTest = testCase
                        ("PropagateExists")
                          (assertEqual " PropagateExists" propagateExistsAST (parseTestRule propagateExistsStr))

existsTest :: TestTree
existsTest          = testCase
                        ("Existence")
                          (assertEqual " Existence" existsAST (parseTestRule existsStr))
singvarTest :: TestTree
singvarTest         = testCase
                        ("SingVar")
                          (assertEqual " Singvar" singvarAST (parseTestRule singvarStr))


{-
 Rule Unparser Unit Tests
 -}
ruleUnparsingTests :: TestTree
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
prop1UnparsingTest :: TestTree
prop1UnparsingTest           = testCase
                                ("Propositional1 Unparsing")
                                   (assertEqual " Propositional1 Unparsing" prop1RuleStr
                                      (show $ pretty prop1RuleAST))

prop2UnparsingTest ::TestTree
prop2UnparsingTest           = testCase
                                ("Propositional2 Unparsing")
                                  (assertEqual " Propositional2 Unparsing" prop2RuleStr
                                      (show $ pretty prop2RuleAST))

prop3UnparsingTest :: TestTree
prop3UnparsingTest           = testCase
                                ("Propositional3 Unparsing")
                                  (assertEqual " Propositional3 Unparsing" prop3RuleStr
                                    (show $ pretty prop3RuleAST))

mpUnparsingTest :: TestTree
mpUnparsingTest              = testCase
                                ("MP Unparsing")
                                  (assertEqual " Propositional3 Unparsing" mpRuleStr
                                    (show $ pretty mpRuleAST))

ugUnparsingTest :: TestTree
ugUnparsingTest              = testCase
                                ("Universal Generalization Unparsing")
                                  (assertEqual " Universal Generalization Unparsing" ugRuleStr
                                    (show $ pretty ugRuleAST))

varSubstUnparsingTest :: TestTree
varSubstUnparsingTest        = testCase
                                ("Variable Substitution Unparsing")
                                  (assertEqual " Variable Substitution Unparsing" varSubstStr
                                    (show $ pretty varSubstAST))

forAllUnparsingTest :: TestTree
forAllUnparsingTest          = testCase
                                ("Forall Unparsing")
                                  (assertEqual " Forall Unparsing" forAllStr
                                    (show $ pretty forAllAST))

framingUnparsingTest :: TestTree
framingUnparsingTest   = testCase
                                ("Framing Unparsing")
                                  (assertEqual " Framing Unparsing" framingStr
                                    (show $ pretty framingAST))
propagateExistsUnparsingTest :: TestTree
propagateExistsUnparsingTest = testCase
                                ("Propagate Exists Unparsing")
                                 (assertEqual " PropagateExists Unparsing" propagateExistsStr
                                  (show $ pretty propagateExistsAST))

propagateOrUnparsingTest :: TestTree
propagateOrUnparsingTest     = testCase
                                ("Propagate Or Unparsing")
                                  (assertEqual " Propagate Or Unparsing" propagateOrStr
                                    (show $ pretty propagateOrAST))

existsUnparsingTest :: TestTree
existsUnparsingTest          = testCase
                                ("Exists Unparsing")
                                 (assertEqual " Exists Unparsing" existsStr
                                  (show $ pretty existsAST))

singvarUnparsingTest :: TestTree
singvarUnparsingTest         = testCase
                                ("Singvar Unparsing")
                                  (assertEqual " Singvar Unparsing" singvarStr
                                    (show $ pretty singvarAST))


