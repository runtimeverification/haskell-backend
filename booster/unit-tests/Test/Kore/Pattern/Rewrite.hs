{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Kore.Pattern.Rewrite (
    test_rewriteStep,
    test_performRewrite,
) where

import Control.Exception (ErrorCall, catch)
import Control.Monad.Logger.CallStack
import Data.ByteString.Char8 (ByteString)
import Data.List.NonEmpty qualified as NE
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import Numeric.Natural
import Test.Tasty
import Test.Tasty.HUnit

import Kore.Definition.Attributes.Base
import Kore.Definition.Base
import Kore.Pattern.Base
import Kore.Pattern.Index (TermIndex (..))
import Kore.Pattern.Rewrite
import Kore.Pattern.Util (sortOfTerm)
import Test.Kore.Fixture

test_rewriteStep :: TestTree
test_rewriteStep =
    testGroup
        "Rewriting"
        [ errorCases
        , rewriteSuccess
        , unifyNotMatch
        , definednessUnclear
        , rewriteStuck
        , rulePriority
        ]

test_performRewrite :: TestTree
test_performRewrite =
    testGroup
        "Iterated rewriting"
        [ -- same tests as above, but calling the iterating function
          canRewrite
        , abortsOnErrors
        , callsError
        , abortsOnFailures
        , supportsDepthControl
        , supportsCutPoints
        , supportsTerminalRules
        ]

----------------------------------------

def :: KoreDefinition
def =
    testDefinition
        { rewriteTheory =
            mkTheory
                [ (TopSymbol "con1", [rule1, rule2, rule1'])
                , (TopSymbol "con3", [rule3])
                , (TopSymbol "con4", [rule4])
                ]
        }

varX, varY :: Term
varX = var "X" someSort
varY = var "Y" someSort

rule1, rule1', rule2, rule3, rule4 :: RewriteRule
rule1 =
    rule
        (Just "con1-f1")
        (termInKCell "RuleVar" (app con1 [d]))
        (termInKCell "RuleVar" (app f1 [d]))
        42
rule1' =
    rule
        (Just "con1-f1'")
        (termInKCell "RuleVar" (app con1 [varX]))
        (termInKCell "RuleVar" (app f1 [varX]))
        50
rule2 =
    rule
        (Just "con1-f2")
        (termInKCell "RuleVar" (app con1 [varX]))
        (termInKCell "RuleVar" (app con4 [varX, varX]))
        50
rule3 =
    rule
        (Just "con3-con1")
        (termInKCell "RuleVar" (app con3 [dv someSort "otherThing", varY]))
        (termInKCell "RuleVar" (app con1 [dv someSort "somethingElse"]))
        42
rule4 =
    ( rule
        (Just "con4-f2-partial")
        (termInKCell "RuleVar" (app con4 [varX, varY]))
        (termInKCell "RuleVar" (app f2 [varY]))
        42
    )
        { computedAttributes = ComputedAxiomAttributes False False
        }

termInKCell :: ByteString -> Term -> Pattern
termInKCell varName = flip Pattern [] . withinKCell varName

-- indexing only works with a K cell. For realistic test, we also use
-- an injection into 'KItem'.
withinKCell :: ByteString -> Term -> Term
withinKCell restVar term =
    app kCell [app kseq [injKItem term, var restVar kItemSort]]

kCell, kseq :: Symbol
kCell =
    Symbol
        { name = "Lbl'-LT-'k'-GT-'"
        , sortVars = []
        , resultSort = kSort -- bogus
        , argSorts = [kSort]
        , attributes = asConstructor
        }
kseq =
    Symbol
        { name = "kseq"
        , sortVars = []
        , resultSort = kSort
        , argSorts = [kItemSort, kSort]
        , attributes = asConstructor
        }

injKItem :: Term -> Term
injKItem t = Injection (sortOfTerm t) kItemSort t

rule :: Maybe Text -> Pattern -> Pattern -> Priority -> RewriteRule
rule ruleLabel lhs rhs priority =
    RewriteRule
        { lhs
        , rhs
        , attributes = AxiomAttributes{location, priority, ruleLabel, simplification = False}
        , computedAttributes = ComputedAxiomAttributes False True
        }
  where
    location = Location "no-file" $ Position 0 0

mkTheory :: [(TermIndex, [RewriteRule])] -> RewriteTheory
mkTheory = Map.map mkPriorityGroups . Map.fromList
  where
    mkPriorityGroups :: [RewriteRule] -> Map Priority [RewriteRule]
    mkPriorityGroups rules =
        Map.unionsWith
            (<>)
            [Map.fromList [(r.attributes.priority, [r])] | r <- rules]

d :: Term
d = dv someSort "thing"

----------------------------------------
errorCases
    , rewriteSuccess
    , unifyNotMatch
    , definednessUnclear
    , rewriteStuck
    , rulePriority ::
        TestTree
errorCases =
    testGroup
        "Simple error cases"
        [ testCase "No rules" $ do
            let pat = termInKCell "Thing" $ app con2 [d]
            pat `failsWith` NoRulesForTerm pat.term
        , testCase "Index is None" $ do
            let pat = termInKCell "Thing" $ AndTerm (app con1 [d]) (app con2 [d])
            pat `failsWith` TermIndexIsNone pat.term
        ]
rewriteSuccess =
    testCase "con1 app rewrites to f1 app" $
        (termInKCell "ConfigVar" $ app con1 [d]) `rewritesTo` (termInKCell "ConfigVar" $ app f1 [d])
unifyNotMatch =
    testCase "Indeterminate case when subject has variables" $ do
        let pat = termInKCell "ConfigVar" $ app con3 [var "X" someSort, d]
            -- "non-match" substitution:
            subst =
                Map.fromList
                    [ (Variable someSort "X", dv someSort "otherThing")
                    , (Variable someSort "Y", d)
                    , (Variable kItemSort "RuleVar", var "ConfigVar" kItemSort)
                    ]
        pat `failsWith` UnificationIsNotMatch rule3 pat.term subst
definednessUnclear =
    testCase "con4 rewrite to f2 might become undefined" $ do
        let pcon4 = termInKCell "ConfigVar" $ app con4 [d, d]
        pcon4 `failsWith` DefinednessUnclear rule4 pcon4
rewriteStuck =
    testCase "con3 app is stuck (no rules apply)" $ do
        let con3App = termInKCell "ConfigVar" $ app con3 [d, d]
        runRewriteM def Nothing (rewriteStep [] [] con3App) @?= Left (NoApplicableRules con3App)
rulePriority =
    testCase "con1 rewrites to a branch when higher priority does not apply" $ do
        let d2 = dv someSort "otherThing"
        (termInKCell "ConfigVar" $ app con1 [d2])
            `branchesTo` [ termInKCell "ConfigVar" $ app con4 [d2, d2]
                         , termInKCell "ConfigVar" $ app f1 [d2]
                         ]

rewritesTo :: Pattern -> Pattern -> IO ()
p1 `rewritesTo` p2 =
    runRewriteM def Nothing (rewriteStep [] [] p1) @?= Right (RewriteSingle p2)

branchesTo :: Pattern -> [Pattern] -> IO ()
p `branchesTo` ps =
    runRewriteM def Nothing (rewriteStep [] [] p) @?= Right (RewriteBranch p $ NE.fromList ps)

failsWith :: Pattern -> RewriteFailed -> IO ()
failsWith p err =
    runRewriteM def Nothing (rewriteStep [] [] p) @?= Left err

----------------------------------------
-- tests for performRewrite (iterated rewrite in IO with logging)

runRewrite :: Pattern -> IO (Natural, RewriteResult Pattern)
runRewrite = runNoLoggingT . performRewrite def Nothing Nothing [] []

aborts :: Term -> IO ()
aborts t = runRewrite (termInKCell "C" t) >>= (@?= (0, RewriteAborted (termInKCell "C" t)))

canRewrite :: TestTree
canRewrite =
    testGroup
        "Can rewrite"
        [ testCase "Rewrites con1 once, then aborts" $ do
            let con1Term = termInKCell "C" $ app con1 [d]
                f1Term = termInKCell "C" $ app f1 [d]
            runRewrite con1Term >>= (@?= (1, RewriteAborted f1Term))
        , testCase "Rewrites con3 twice, branching on con1" $ do
            let rule3Dv1 = dv someSort "otherThing"
                rule3Dv2 = dv someSort "somethingElse"
                con3Term = termInKCell "C" $ app con3 [rule3Dv1, d]
                con1Term = termInKCell "C" $ app con1 [rule3Dv2]
                branch1 = termInKCell "C" $ app con4 [rule3Dv2, rule3Dv2]
                branch2 = termInKCell "C" $ app f1 [rule3Dv2]
            runRewrite con3Term
                >>= (@?= (1, RewriteBranch con1Term (NE.fromList [branch1, branch2])))
        , testCase "Returns stuck when no rules could be applied" $ do
            let con3NoRules = termInKCell "C" $ app con3 [d, d]
            runRewrite con3NoRules >>= (@?= (0, RewriteStuck con3NoRules))
        ]

abortsOnErrors :: TestTree
abortsOnErrors =
    testGroup
        "Aborts rewrite when there is an error"
        [ testCase "when there are no rules at all" $ aborts (app con2 [d])
        , testCase "when the term index is None" $
            aborts (AndTerm (app con1 [d]) (app con2 [d]))
        ]

callsError :: TestTree
callsError =
    testGroup
        "Calls error when there are unexpected situations"
        [ testCase "on wrong argument count in a symbol application" $ do
            (runRewrite (termInKCell "C" $ app con1 [d, d, d]) >> assertFailure "success")
                `catch` (\(_ :: ErrorCall) -> pure ())
        ]

abortsOnFailures :: TestTree
abortsOnFailures =
    testGroup
        "Aborts rewrite when the rewriter cannot handle it"
        [ testCase "when unification is not a match" $ aborts (app con3 [var "X" someSort, d])
        , testCase "when definedness is unclear" $ aborts (app con4 [d, d])
        ]

supportsDepthControl :: TestTree
supportsDepthControl =
    testGroup
        "supports maximum depth control"
        [ testCase "executes normally when maxDepth > maximum expected" $
            runRewriteDepth 42 con1Term >>= (@?= (1, RewriteAborted f1Term))
        , testCase "stops execution after 1 step when maxDepth == 1" $
            runRewriteDepth 1 con1Term >>= (@?= (1, RewriteStopped f1Term))
        , testCase "performs no steps when maxDepth == 0" $
            runRewriteDepth 0 con1Term >>= (@?= (0, RewriteStopped con1Term))
        , testCase "prefers reporting branches to stopping at depth" $ do
            let rule3Dv1 = dv someSort "otherThing"
                rule3Dv2 = dv someSort "somethingElse"
                con3Term = termInKCell "C" $ app con3 [rule3Dv1, d]
                con1Dv2 = termInKCell "C" $ app con1 [rule3Dv2]
                branch1 = termInKCell "C" $ app con4 [rule3Dv2, rule3Dv2]
                branch2 = termInKCell "C" $ app f1 [rule3Dv2]
            runRewriteDepth 2 con3Term
                >>= (@?= (1, RewriteBranch con1Dv2 (NE.fromList [branch1, branch2])))
        ]
  where
    con1Term = termInKCell "C" $ app con1 [d]
    f1Term = termInKCell "C" $ app f1 [d]
    runRewriteDepth :: Natural -> Pattern -> IO (Natural, RewriteResult Pattern)
    runRewriteDepth depth =
        runNoLoggingT . performRewrite def Nothing (Just depth) [] []

supportsCutPoints :: TestTree
supportsCutPoints =
    testGroup
        "supports cut-point labels"
        [ testCase "stops at a cut-point label" $
            runRewriteCutPoint "con1-f1" con1Term
                >>= (@?= (0, RewriteCutPoint "con1-f1" con1Term f1Term))
        , testCase "ignores non-matching cut-point labels" $
            runRewriteCutPoint "otherLabel" con1Term
                >>= (@?= (1, RewriteAborted f1Term))
        , testCase "prefers reporting branches to stopping at label in one branch" $ do
            let rule3Dv1 = dv someSort "otherThing"
                rule3Dv2 = dv someSort "somethingElse"
                con3Term = termInKCell "C" $ app con3 [rule3Dv1, d]
                con1Dv2 = termInKCell "C" $ app con1 [rule3Dv2]
                branch1 = termInKCell "C" $ app con4 [rule3Dv2, rule3Dv2]
                branch2 = termInKCell "C" $ app f1 [rule3Dv2]
            runRewriteCutPoint "con1-f2" con3Term
                >>= (@?= (1, RewriteBranch con1Dv2 (NE.fromList [branch1, branch2])))
        ]
  where
    con1Term = termInKCell "C" $ app con1 [d]
    f1Term = termInKCell "C" $ app f1 [d]
    runRewriteCutPoint :: Text -> Pattern -> IO (Natural, RewriteResult Pattern)
    runRewriteCutPoint lbl =
        runNoLoggingT . performRewrite def Nothing Nothing [lbl] []

supportsTerminalRules :: TestTree
supportsTerminalRules =
    testGroup
        "supports cut-point labels"
        [ testCase "stops at a terminal rule label" $
            runRewriteTerminal "con1-f1" con1Term
                >>= (@?= (1, RewriteTerminal "con1-f1" f1Term))
        , testCase "ignores non-matching labels" $
            runRewriteTerminal "otherLabel" con1Term
                >>= (@?= (1, RewriteAborted f1Term))
        ]
  where
    con1Term = termInKCell "C" $ app con1 [d]
    f1Term = termInKCell "C" $ app f1 [d]
    runRewriteTerminal :: Text -> Pattern -> IO (Natural, RewriteResult Pattern)
    runRewriteTerminal lbl =
        runNoLoggingT . performRewrite def Nothing Nothing [] [lbl]
