module Test.Kore.Simplify.Rule (test_simplifyRulePattern) where

import Kore.Internal.TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
    mkRewritingTerm,
 )
import Kore.Rewrite.RulePattern (
    RulePattern,
    rulePattern,
 )
import qualified Kore.Simplify.Rule as Kore
import Prelude.Kore
import qualified Test.Kore.Builtin.Bool as Test.Bool
import qualified Test.Kore.Builtin.Builtin as Builtin
import qualified Test.Kore.Builtin.Definition as Builtin
import qualified Test.Kore.Builtin.Int as Test.Int
import Test.Kore.Simplify
import Test.Tasty
import Test.Tasty.HUnit

test_simplifyRulePattern :: [TestTree]
test_simplifyRulePattern =
    [ simplifies
        "simplifies \\and (#as) patterns"
        (rulePattern (andBool (mkAnd false x) y) x)
        (rulePattern (andBool false y) false)
    , notSimplifies
        "does not simplify disjunctions"
        (rulePattern (andBool (mkOr true x) y) (mkOr y (andBool x y)))
    , notSimplifies
        "does not simplify builtins"
        (rulePattern (sizeList unitList) (mkInt 0))
    ]
  where
    andBool = Builtin.andBool
    unitList = Builtin.unitList
    sizeList = Builtin.sizeList
    x = mkElemVar (mkElementVariable "x" Builtin.boolSort) & mkRewritingTerm
    y = mkElemVar (mkElementVariable "y" Builtin.boolSort) & mkRewritingTerm
    mkBool = Test.Bool.asInternal
    true = mkBool True
    false = mkBool False
    mkInt = Test.Int.asInternal

withSimplified ::
    TestName ->
    (RulePattern RewritingVariableName -> Assertion) ->
    RulePattern RewritingVariableName ->
    TestTree
withSimplified testName check origin =
    testCase testName (check =<< simplifyRulePattern origin)

simplifies ::
    TestName ->
    RulePattern RewritingVariableName ->
    RulePattern RewritingVariableName ->
    TestTree
simplifies testName origin expect =
    withSimplified testName (assertEqual "" expect) origin

notSimplifies ::
    TestName ->
    RulePattern RewritingVariableName ->
    TestTree
notSimplifies testName origin =
    withSimplified testName (assertEqual "" origin) origin

simplifyRulePattern ::
    RulePattern RewritingVariableName ->
    IO (RulePattern RewritingVariableName)
simplifyRulePattern = runSimplifier Builtin.testEnv . Kore.simplifyRulePattern
