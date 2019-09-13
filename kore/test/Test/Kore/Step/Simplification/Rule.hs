module Test.Kore.Step.Simplification.Rule
    ( test_simplifyRulePattern ) where

import Test.Tasty
import Test.Tasty.HUnit

import Kore.Internal.TermLike
import Kore.Step.Rule
    ( RulePattern
    , rulePattern
    )
import qualified Kore.Step.Simplification.Rule as Kore

import qualified Test.Kore.Builtin.Bool as Test.Bool
import qualified Test.Kore.Builtin.Builtin as Builtin
import qualified Test.Kore.Builtin.Definition as Builtin
import qualified Test.Kore.Builtin.Int as Test.Int
import Test.Kore.Step.Simplification

test_simplifyRulePattern :: [TestTree]
test_simplifyRulePattern =
    [ simplifies    "simplifies \\and (#as) patterns"
        (rulePattern (andBool (mkAnd false x) y) x    )
        (rulePattern (andBool false           y) false)
    , notSimplifies "does not simplify disjunctions"
        (rulePattern (andBool (mkOr true x) y) (mkOr y (andBool x y)))
    , notSimplifies "does not simplify builtins"
        (rulePattern (sizeList unitList) (mkInt 0))
    ]
  where
    andBool = Builtin.andBool
    unitList = Builtin.unitList
    sizeList = Builtin.sizeList
    x = mkElemVar (elemVarS "x" Builtin.boolSort)
    y = mkElemVar (elemVarS "y" Builtin.boolSort)
    mkBool = Test.Bool.asInternal
    true = mkBool True
    false = mkBool False
    mkInt = Test.Int.asInternal

withSimplified
    :: TestName
    -> (RulePattern Variable -> Assertion)
    -> RulePattern Variable
    -> TestTree
withSimplified testName check origin =
    testCase testName (check =<< simplifyRulePattern origin)

simplifies
    :: TestName
    -> RulePattern Variable
    -> RulePattern Variable
    -> TestTree
simplifies testName origin expect =
    withSimplified testName (assertEqual "" expect) origin

notSimplifies
    :: TestName
    -> RulePattern Variable
    -> TestTree
notSimplifies testName origin =
    withSimplified testName (assertEqual "" origin) origin

simplifyRulePattern :: RulePattern Variable -> IO (RulePattern Variable)
simplifyRulePattern = runSimplifier Builtin.testEnv . Kore.simplifyRulePattern
