{-# LANGUAGE QuasiQuotes #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Pattern.Rewrite (
    test_rewriteStep,
    test_performRewrite,
) where

import Control.Exception (ErrorCall, catch)
import Control.Monad.Logger.CallStack
import Data.List.NonEmpty qualified as NE
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Text (Text)
import Numeric.Natural
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.Pattern.Base
import Booster.Pattern.Index (TermIndex (..))
import Booster.Pattern.Rewrite
import Booster.Syntax.Json.Internalise (trm)
import Booster.Syntax.ParsedKore.Internalise (symb)
import Test.Booster.Fixture hiding (inj)

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

inj :: Symbol
inj = injectionSymbol

rule1, rule1', rule2, rule3, rule4 :: RewriteRule "Rewrite"
rule1 =
    rule
        (Just "con1-f1")
        ( Pattern
            [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), RuleVar:SortK{}) ) |]
            []
        )
        ( Pattern
            [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}(   \dv{SomeSort{}}("thing") ) ), RuleVar:SortK{}) ) |]
            []
        )
        42
rule1' =
    rule
        (Just "con1-f1'")
        ( Pattern
            [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( X:SomeSort{} ) ), RuleVar:SortK{}) ) |]
            []
        )
        ( Pattern
            [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}(   X:SomeSort{} ) ), RuleVar:SortK{}) ) |]
            []
        )
        50
rule2 =
    rule
        (Just "con1-f2")
        ( Pattern
            [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( X:SomeSort{} ) ),                  RuleVar:SortK{}) ) |]
            []
        )
        ( Pattern
            [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( X:SomeSort{}, X:SomeSort{} ) ), RuleVar:SortK{}) ) |]
            []
        )
        50
rule3 =
    rule
        (Just "con3-con1")
        ( Pattern
            [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con3{}( \dv{SomeSort{}}("otherThing"), Y:SomeSort{} ) ), RuleVar:SortK{}) ) |]
            []
        )
        ( Pattern
            [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("somethingElse") ) ),            RuleVar:SortK{}) ) |]
            []
        )
        42
rule4 =
    rule
        (Just "con4-f2-partial")
        ( Pattern
            [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( X:SomeSort{}, Y:SomeSort{} ) ), RuleVar:SortK{}) ) |]
            []
        )
        ( Pattern
            [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f2{}(   Y:SomeSort{} ) ), RuleVar:SortK{}) ) |]
            []
        )
        42
        `withComputedAttributes` ComputedAxiomAttributes False [UndefinedSymbol "f2"]

kCell, kseq :: Symbol
kCell =
    [symb| symbol Lbl'-LT-'k'-GT-'{}(SortK{}) : SortKCell{} [constructor{}()] |]
kseq =
    [symb| symbol kseq{}(SortKItem{}, SortK{}) : SortK{} [constructor{}()] |]

rule :: Maybe Text -> Pattern -> Pattern -> Priority -> RewriteRule "Rewrite"
rule ruleLabel lhs rhs priority =
    RewriteRule
        { lhs = lhs.term
        , rhs = rhs.term
        , requires = lhs.constraints
        , ensures = rhs.constraints
        , attributes =
            AxiomAttributes
                { location = Nothing
                , priority
                , ruleLabel
                , simplification = Flag False
                , preserving = Flag False
                , concreteness = Unconstrained
                , uniqueId = Nothing
                }
        , computedAttributes = ComputedAxiomAttributes False []
        , existentials = mempty
        }

withComputedAttributes :: RewriteRule r -> ComputedAxiomAttributes -> RewriteRule r
r@RewriteRule{lhs} `withComputedAttributes` computedAttributes =
    r{lhs, computedAttributes}

mkTheory :: [(TermIndex, [RewriteRule "Rewrite"])] -> Theory (RewriteRule "Rewrite")
mkTheory = Map.map mkPriorityGroups . Map.fromList
  where
    mkPriorityGroups :: [RewriteRule "Rewrite"] -> Map Priority [RewriteRule "Rewrite"]
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
        [ testCase "No rules" $
            [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con2{}( \dv{SomeSort{}}("thing") ) ), Thing:SortK{}) ) |]
                `failsWith` NoRulesForTerm
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con2{}( \dv{SomeSort{}}("thing") ) ), Thing:SortK{}) ) |]
        , testCase "Index is None" $ do
            let t =
                    [trm| 
                        kCell{}( 
                            kseq{}( 
                                inj{SomeSort{}, SortKItem{}}( 
                                    \and{SomeSort{}}( 
                                        con1{}( \dv{SomeSort{}}("thing") ), 
                                        con2{}( \dv{SomeSort{}}("thing") )
                                    )
                                ), 
                                Thing:SortK{}
                            )
                        ) 
                    |]
            t `failsWith` TermIndexIsNone t
        ]
rewriteSuccess =
    testCase "con1 app rewrites to f1 app" $
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), ConfigVar:SortK{}) ) |]
            `rewritesTo` ( "con1-f1"
                         , [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}(   \dv{SomeSort{}}("thing") ) ), ConfigVar:SortK{}) ) |]
                         )
unifyNotMatch =
    testCase "Indeterminate case when subject has variables" $ do
        let t =
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con3{}( X:SomeSort{}, \dv{SomeSort{}}("thing") ) ), ConfigVar:SortK{}) ) |]
            -- "non-match" substitution:
            subst =
                Map.fromList
                    [ (Variable someSort "X", dv someSort "otherThing")
                    , (Variable someSort "Y", d)
                    , (Variable kSort "RuleVar", var "ConfigVar" kSort)
                    ]
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con3{}( X:SomeSort{}, \dv{SomeSort{}}("thing") ) ), ConfigVar:SortK{}) ) |]
            `failsWith` UnificationIsNotMatch rule3 t subst
definednessUnclear =
    testCase "con4 rewrite to f2 might become undefined" $ do
        let pcon4 =
                [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( \dv{SomeSort{}}("thing"), \dv{SomeSort{}}("thing") ) ), ConfigVar:SortK{}) ) |]
        pcon4 `failsWith` DefinednessUnclear rule4 (Pattern pcon4 []) [UndefinedSymbol "f2"]
rewriteStuck =
    testCase "con3 app is stuck (no rules apply)" $ do
        let con3App =
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con3{}( \dv{SomeSort{}}("thing"), \dv{SomeSort{}}("thing") ) ), ConfigVar:SortK{}) ) |]
        con3App `failsWith` NoApplicableRules (Pattern con3App [])
rulePriority =
    testCase "con1 rewrites to a branch when higher priority does not apply" $
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("otherThing") ) ), ConfigVar:SortK{}) ) |]
            `branchesTo` [
                             ( "con1-f2"
                             , [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( \dv{SomeSort{}}("otherThing"), \dv{SomeSort{}}("otherThing") ) ), ConfigVar:SortK{}) ) |]
                             )
                         ,
                             ( "con1-f1'"
                             , [trm| kCell{}( kseq{}( inj{SomeSort{},    SortKItem{}}( f1{}(   \dv{SomeSort{}}("otherThing")                                ) ), ConfigVar:SortK{}) ) |]
                             )
                         ]

rewritesTo :: Term -> (Text, Term) -> IO ()
t1 `rewritesTo` (lbl, t2) =
    runRewriteM def Nothing (rewriteStep [] [] $ Pattern t1 [])
        @?= Right (RewriteFinished (Just lbl) Nothing $ Pattern t2 [])

branchesTo :: Term -> [(Text, Term)] -> IO ()
t `branchesTo` ts =
    runRewriteM def Nothing (rewriteStep [] [] $ Pattern t [])
        @?= Right
            (RewriteBranch (Pattern t []) $ NE.fromList $ map (\(lbl, t') -> (lbl, Nothing, Pattern t' [])) ts)

failsWith :: Term -> RewriteFailed "Rewrite" -> IO ()
failsWith t err =
    runRewriteM def Nothing (rewriteStep [] [] $ Pattern t []) @?= Left err

----------------------------------------
-- tests for performRewrite (iterated rewrite in IO with logging)

runRewrite :: Term -> IO (Natural, RewriteResult Term)
runRewrite t = do
    (counter, _, res) <- runNoLoggingT $ performRewrite def Nothing Nothing [] [] $ Pattern t []
    pure (counter, fmap (.term) res)

aborts :: Term -> IO ()
aborts t = runRewrite t >>= (@?= (0, RewriteAborted t))

newtype Steps = Steps Natural

rewrites :: Steps -> Term -> t -> (t -> RewriteResult Term) -> IO ()
rewrites (Steps n) t t' f =
    runRewrite t >>= (@?= (n, f t'))

canRewrite :: TestTree
canRewrite =
    testGroup
        "Can rewrite"
        [ testCase "Rewrites con1 once, then aborts" $
            rewrites
                (Steps 1)
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}(   \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                RewriteAborted
        , testCase "Rewrites con3 twice, branching on con1" $ do
            let branch1 =
                    ( "con1-f2"
                    , Nothing
                    , [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( \dv{SomeSort{}}("somethingElse"), \dv{SomeSort{}}("somethingElse") ) ), C:SortK{}) ) |]
                    )
                branch2 =
                    ( "con1-f1'"
                    , Nothing
                    , [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}(    f1{}(   \dv{SomeSort{}}("somethingElse")                                   ) ), C:SortK{}) ) |]
                    )

            rewrites
                (Steps 1)
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con3{}( \dv{SomeSort{}}("otherThing"), \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("somethingElse")                        ) ), C:SortK{}) ) |]
                (`RewriteBranch` NE.fromList [branch1, branch2])
        , testCase "Returns stuck when no rules could be applied" $ do
            rewrites
                (Steps 0)
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con3{}( \dv{SomeSort{}}("thing"), \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con3{}( \dv{SomeSort{}}("thing"), \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                RewriteStuck
        ]

abortsOnErrors :: TestTree
abortsOnErrors =
    testGroup
        "Aborts rewrite when there is an error"
        [ testCase "when there are no rules at all" $ aborts (app con2 [d])
        , testCase "when the term index is None" $
            aborts
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( \and{SomeSort{}}( con1{}( \dv{SomeSort{}}("thing") ), con2{}( \dv{SomeSort{}}("thing") ) ) ), C:SortK{} ) ) |]
        ]

callsError :: TestTree
callsError =
    testGroup
        "Calls error when there are unexpected situations"
        [ testCase "on wrong argument count in a symbol application" $ do
            ( runRewrite
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing"), \dv{SomeSort{}}("thing"), \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                    >> assertFailure "success"
                )
                `catch` (\(_ :: ErrorCall) -> pure ())
        ]

abortsOnFailures :: TestTree
abortsOnFailures =
    testGroup
        "Aborts rewrite when the rewriter cannot handle it"
        [ testCase "when unification is not a match" $
            aborts [trm| con3{}(X:SomeSort{}, \dv{SomeSort{}}("thing")) |]
        , testCase "when definedness is unclear" $
            aborts [trm| con4{}(\dv{SomeSort{}}("thing"), \dv{SomeSort{}}("thing")) |]
        ]

newtype MaxDepth = MaxDepth Natural

supportsDepthControl :: TestTree
supportsDepthControl =
    testGroup
        "supports maximum depth control"
        [ testCase "executes normally when maxDepth > maximum expected" $
            rewritesToDepth
                (MaxDepth 42)
                (Steps 1)
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                RewriteAborted
        , testCase "stops execution after 1 step when maxDepth == 1" $
            rewritesToDepth
                (MaxDepth 1)
                (Steps 1)
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                (RewriteFinished Nothing Nothing)
        , testCase "performs no steps when maxDepth == 0" $
            rewritesToDepth
                (MaxDepth 0)
                (Steps 0)
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                (RewriteFinished Nothing Nothing)
        , testCase "prefers reporting branches to stopping at depth" $ do
            let branch1 =
                    ( "con1-f2"
                    , Nothing
                    , [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( \dv{SomeSort{}}("somethingElse"), \dv{SomeSort{}}("somethingElse") ) ), C:SortK{}) ) |]
                    )
                branch2 =
                    ( "con1-f1'"
                    , Nothing
                    , [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}(    f1{}(   \dv{SomeSort{}}("somethingElse")                                   ) ), C:SortK{}) ) |]
                    )

            rewritesToDepth
                (MaxDepth 2)
                (Steps 1)
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con3{}( \dv{SomeSort{}}("otherThing"), \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("somethingElse")                        ) ), C:SortK{}) ) |]
                (`RewriteBranch` NE.fromList [branch1, branch2])
        ]
  where
    rewritesToDepth :: MaxDepth -> Steps -> Term -> t -> (t -> RewriteResult Term) -> IO ()
    rewritesToDepth (MaxDepth depth) (Steps n) t t' f = do
        (counter, _, res) <- runNoLoggingT $ performRewrite def Nothing (Just depth) [] [] $ Pattern t []
        (counter, fmap (.term) res) @?= (n, f t')

supportsCutPoints :: TestTree
supportsCutPoints =
    testGroup
        "supports cut-point labels"
        [ testCase "stops at a cut-point label" $
            rewritesToCutPoint
                "con1-f1"
                (Steps 0)
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                ( RewriteCutPoint
                    "con1-f1"
                    Nothing
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                )
        , testCase "ignores non-matching cut-point labels" $
            rewritesToCutPoint
                "otherLabel"
                (Steps 1)
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                RewriteAborted
        , testCase "prefers reporting branches to stopping at label in one branch" $ do
            let branch1 =
                    ( "con1-f2"
                    , Nothing
                    , [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( \dv{SomeSort{}}("somethingElse"), \dv{SomeSort{}}("somethingElse") ) ), C:SortK{}) ) |]
                    )
                branch2 =
                    ( "con1-f1'"
                    , Nothing
                    , [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}(    f1{}(   \dv{SomeSort{}}("somethingElse")                                   ) ), C:SortK{}) ) |]
                    )

            rewritesToCutPoint
                "con1-f2"
                (Steps 1)
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con3{}( \dv{SomeSort{}}("otherThing"), \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("somethingElse")                        ) ), C:SortK{}) ) |]
                (`RewriteBranch` NE.fromList [branch1, branch2])
        ]
  where
    rewritesToCutPoint :: Text -> Steps -> Term -> t -> (t -> RewriteResult Term) -> IO ()
    rewritesToCutPoint lbl (Steps n) t t' f = do
        (counter, _, res) <- runNoLoggingT $ performRewrite def Nothing Nothing [lbl] [] $ Pattern t []
        (counter, fmap (.term) res) @?= (n, f t')

supportsTerminalRules :: TestTree
supportsTerminalRules =
    testGroup
        "supports cut-point labels"
        [ testCase "stops at a terminal rule label" $
            rewritesToTerminal
                "con1-f1"
                (Steps 1)
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                (RewriteTerminal "con1-f1" Nothing)
        , testCase "ignores non-matching labels" $
            rewritesToTerminal
                "otherLabel"
                (Steps 1)
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                RewriteAborted
        ]
  where
    rewritesToTerminal :: Text -> Steps -> Term -> t -> (t -> RewriteResult Term) -> IO ()
    rewritesToTerminal lbl (Steps n) t t' f = do
        (counter, _, res) <- runNoLoggingT $ performRewrite def Nothing Nothing [] [lbl] $ Pattern t []
        (counter, fmap (.term) res) @?= (n, f t')
