{-# LANGUAGE QuasiQuotes #-}

{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Test.Booster.Pattern.Rewrite (
    test_rewriteStep,
    test_performRewrite,
) where

import Control.Monad.Logger.CallStack
import Data.Bifunctor (second)
import Data.List.NonEmpty qualified as NE
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import Numeric.Natural
import Test.Tasty
import Test.Tasty.HUnit

import Booster.Definition.Attributes.Base
import Booster.Definition.Base
import Booster.Log (Logger (..))
import Booster.Pattern.Base
import Booster.Pattern.Bool
import Booster.Pattern.Index (CellIndex (..), TermIndex (..))
import Booster.Pattern.Pretty (ModifiersRep (..))
import Booster.Pattern.Rewrite
import Booster.SMT.Interface (noSolver)
import Booster.Syntax.Json.Internalise (trm)
import Booster.Syntax.ParsedKore.Internalise (symb)
import Booster.Util (Flag (..))
import Test.Booster.Fixture hiding (inj)
import Test.Booster.Util ((@?>>=))

test_rewriteStep :: TestTree
test_rewriteStep =
    testGroup
        "Rewriting"
        [ errorCases
        , rewriteSuccess
        , subjectVariables
        , definednessUnclear
        , rewriteStuck
        , rulePriority
        , indeterminatePruning
        ]

test_performRewrite :: TestTree
test_performRewrite =
    testGroup
        "Iterated rewriting"
        [ -- same tests as above, but calling the iterating function
          canRewrite
        , abortsOnProblems
        , supportsDepthControl
        , supportsCutPoints
        , supportsTerminalRules
        ]

----------------------------------------

indexC :: SymbolName -> TermIndex
indexC = TermIndex . (: []) . IdxCons

def :: KoreDefinition
def =
    testDefinition
        { rewriteTheory =
            mkTheory
                [ (indexC "con1", [rule1, rule2, rule1'])
                , (indexC "con3", [rule3])
                , (indexC "con4", [rule4])
                , (indexC "conBoolPair", [ruleBoolGuarded, ruleBoolCatchAll])
                ]
        }

inj :: Symbol
inj = injectionSymbol

rule1, rule1', rule2, rule3, rule4 :: RewriteRule "Rewrite"
rule1 =
    rule
        (Just "con1-f1")
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), RuleVar:SortK{}) ) |]
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}(   \dv{SomeSort{}}("thing") ) ), RuleVar:SortK{}) ) |]
        42
rule1' =
    rule
        (Just "con1-f1'")
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( X:SomeSort{} ) ), RuleVar:SortK{}) ) |]
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}(   X:SomeSort{} ) ), RuleVar:SortK{}) ) |]
        50
rule2 =
    rule
        (Just "con1-f2")
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( X:SomeSort{} ) ),                  RuleVar:SortK{}) ) |]
        [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( X:SomeSort{}, X:SomeSort{} ) ), RuleVar:SortK{}) ) |]
        50
rule3 =
    rule
        (Just "con3-con1")
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con3{}( \dv{SomeSort{}}("otherThing"), Y:SomeSort{} ) ), RuleVar:SortK{}) ) |]
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("somethingElse") ) ),            RuleVar:SortK{}) ) |]
        42
rule4 =
    rule
        (Just "con4-f2-partial")
        [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( X:SomeSort{}, Y:SomeSort{} ) ), RuleVar:SortK{}) ) |]
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f2{}(   Y:SomeSort{} ) ), RuleVar:SortK{}) ) |]
        42
        `withComputedAttributes` ComputedAxiomAttributes False [UndefinedSymbol "f2"]

{- | High-priority rule for the indeterminate-pruning tests.

LHS expects a concrete @"trigger"@ in the @SomeSort@ slot and binds a
@SortBool@ rule variable @P@ in the second slot. The rule's @requires@ is
just that variable: under any substitution that binds @P@ to a concrete
'FalseBool', the @requires@ trivially evaluates to bottom. Under the
proposed fix, an indeterminate match on this rule whose partial
substitution happens to bind @P ↦ FalseBool@ will be pruned ('returnNotApplied')
rather than aborting the whole rewrite step.
-}
ruleBoolGuarded :: RewriteRule "Rewrite"
ruleBoolGuarded =
    ( ruleWithRequires
        (Just "conBoolPair-guarded")
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( conBoolPair{}( \dv{SomeSort{}}("trigger"), P:SortBool{} ) ), RuleVar:SortK{}) ) |]
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}(           \dv{SomeSort{}}("via-guarded")                ) ), RuleVar:SortK{}) ) |]
        42
        [Predicate [trm| P:SortBool{} |]]
    )

{- | Catch-all rule for the indeterminate-pruning tests; lower priority than
'ruleBoolGuarded' and unconditionally applicable.
-}
ruleBoolCatchAll :: RewriteRule "Rewrite"
ruleBoolCatchAll =
    rule
        (Just "conBoolPair-catchall")
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( conBoolPair{}( AnyX:SomeSort{}, AnyQ:SortBool{} ) ), RuleVar:SortK{}) ) |]
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}(           \dv{SomeSort{}}("via-catchall")               ) ), RuleVar:SortK{}) ) |]
        50

kCell :: Symbol
kCell =
    [symb| symbol Lbl'-LT-'k'-GT-'{}(SortK{}) : SortKCell{} [constructor{}()] |]

rule :: Maybe Text -> Term -> Term -> Priority -> RewriteRule "Rewrite"
rule ruleLabel lhs rhs priority =
    RewriteRule
        { lhs
        , rhs
        , requires = []
        , ensures = []
        , attributes =
            AxiomAttributes
                { location = Nothing
                , priority
                , ruleLabel
                , simplification = Flag False
                , preserving = Flag False
                , concreteness = Unconstrained
                , uniqueId = mockUniqueId
                , smtLemma = Flag False
                }
        , computedAttributes = ComputedAxiomAttributes False []
        , existentials = mempty
        }

ruleWithRequires :: Maybe Text -> Term -> Term -> Priority -> [Predicate] -> RewriteRule "Rewrite"
ruleWithRequires lbl lhs rhs prio reqs =
    (rule lbl lhs rhs prio){requires = reqs}

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

testConf :: IO RewriteConfig
testConf = do
    smtSolver <- noSolver
    pure
        RewriteConfig
            { definition = def
            , llvmApi = Nothing
            , smtSolver
            , varsToAvoid = mempty
            , doTracing = NoCollectRewriteTraces
            , logger = Logger $ const $ pure ()
            , prettyModifiers = ModifiersRep @'[] Proxy
            , mbMaxDepth = Nothing
            , mbSimplify = Nothing
            , cutLabels = []
            , terminalLabels = []
            }

----------------------------------------
errorCases
    , rewriteSuccess
    , subjectVariables
    , definednessUnclear
    , rewriteStuck
    , rulePriority
    , indeterminatePruning ::
        TestTree
errorCases =
    testGroup
        "Simple error cases"
        [ testCase "Index is IdxNone" $ do
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
subjectVariables =
    testCase "Aborts case when subject has variables" $ do
        let t =
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con3{}( X:SomeSort{}, \dv{SomeSort{}}("thing") ) ), ConfigVar:SortK{}) ) |]
        t
            `failsWith` RuleApplicationUnclear
                rule3
                t
                (NE.singleton ([trm| \dv{SomeSort{}}("otherThing")|], [trm| X:SomeSort{} |]))
definednessUnclear =
    testCase "con4 rewrite to f2 might become undefined" $ do
        let pcon4 =
                [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( \dv{SomeSort{}}("thing"), \dv{SomeSort{}}("thing") ) ), ConfigVar:SortK{}) ) |]
        pcon4 `failsWith` DefinednessUnclear rule4 (Pattern_ pcon4) [UndefinedSymbol "f2"]
rewriteStuck =
    testGroup
        "Stuck states"
        [ testCase "con3 app is stuck (no rules apply)" $ do
            let con3App =
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con3{}( \dv{SomeSort{}}("thing"), \dv{SomeSort{}}("thing") ) ), ConfigVar:SortK{}) ) |]
            getsStuck con3App
        , testCase "No rules for con2" $
            getsStuck
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con2{}( \dv{SomeSort{}}("thing") ) ), Thing:SortK{}) ) |]
        , testCase "No rules for dotk()" $
            getsStuck
                [trm| kCell{}( dotk{}() ) |]
        ]
indeterminatePruning =
    testGroup
        "Pruning indeterminate matches via partial substitution"
        -- These tests exercise the contract that, when 'matchTerms' returns
        -- 'MatchIndeterminate' for a rule, 'applyRule' uses the partial
        -- substitution carried alongside the remainder pairs to evaluate the
        -- rule's 'requires' clause. If any clause simplifies to syntactic
        -- 'FalseBool' under that partial substitution, the rule is pruned
        -- ('returnNotApplied') instead of aborting the whole step. If no
        -- clause can be proved false, the existing 'RuleApplicationUnclear'
        -- abort fires as today.
        --
        -- Setup (in module 'def'):
        --   * 'ruleBoolGuarded' (priority 42): matches
        --     'conBoolPair("trigger", P:SortBool)', 'requires = [P]'.
        --   * 'ruleBoolCatchAll' (priority 50): matches
        --     'conBoolPair(_, _)' unconditionally, rewrites to a marker.
        -- A subject of the form 'conBoolPair(VSub, b)' where VSub is a
        -- subject-side variable forces 'MatchIndeterminate' against
        -- 'ruleBoolGuarded' (the pattern's "trigger" cannot unify with the
        -- variable). The matcher does, however, bind 'P ↦ b' in the partial
        -- substitution; 'b' decides whether the rule can be pruned.
        [ testCase "Indeterminate match is pruned when requires under partial sub is FalseBool" $
            -- Today (no pruning): aborts with RuleApplicationUnclear on ruleBoolGuarded.
            -- After fix: ruleBoolGuarded is pruned because requires becomes [Predicate FalseBool];
            -- ruleBoolCatchAll is the only applicable rule and fires.
            [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( conBoolPair{}( VSub:SomeSort{}, \dv{SortBool{}}("false") ) ), ConfigVar:SortK{}) ) |]
                `rewritesTo` ( "conBoolPair-catchall"
                             , [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}( \dv{SomeSort{}}("via-catchall") ) ), ConfigVar:SortK{}) ) |]
                             )
        , -- Note: a third case ("requires under partial sub is a free Bool variable
          -- — cannot prune, must abort") would exercise the SMT-discharge branch
          -- of 'checkRequires'. The unit test config uses 'noSolver', so we leave
          -- that case to the rpc-integration test (the real KEVM `#addr` repro).
          testCase "Indeterminate match still aborts when requires under partial sub is TrueBool" $
            -- The partial sub binds P ↦ TrueBool, so the substituted requires is trivially true
            -- (not bottom). The rule's match is still indeterminate, so the impl must discard the
            -- "requires is satisfied" outcome and abort — pruning only fires on a *concretely
            -- false* requires. Behaviour is unchanged from today (abort either way), but this
            -- locks in that the impl does not accidentally treat the rule as applicable.
            let t =
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( conBoolPair{}( VSub:SomeSort{}, \dv{SortBool{}}("true") ) ), ConfigVar:SortK{}) ) |]
             in t
                    `failsWith` RuleApplicationUnclear
                        ruleBoolGuarded
                        t
                        (NE.singleton ([trm| \dv{SomeSort{}}("trigger")|], [trm| VSub:SomeSort{} |]))
        ]
rulePriority =
    testCase "con1 rewrites to a branch when higher priority does not apply" $
        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("otherThing") ) ), ConfigVar:SortK{}) ) |]
            `branchesTo` [
                             ( "con1-f2"
                             , [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( \dv{SomeSort{}}("otherThing"), \dv{SomeSort{}}("otherThing") ) ), ConfigVar:SortK{}) ) |]
                             , Predicate TrueBool
                             , Map.fromList
                                [
                                    ( Variable someSort "X"
                                    , [trm| \dv{SomeSort{}}("otherThing") |]
                                    )
                                ,
                                    ( Variable SortK "RuleVar"
                                    , [trm| ConfigVar:SortK{} |]
                                    )
                                ]
                             )
                         ,
                             ( "con1-f1'"
                             , [trm| kCell{}( kseq{}( inj{SomeSort{},    SortKItem{}}( f1{}(   \dv{SomeSort{}}("otherThing")                                ) ), ConfigVar:SortK{}) ) |]
                             , Predicate TrueBool
                             , Map.fromList
                                [
                                    ( Variable someSort "X"
                                    , [trm| \dv{SomeSort{}}("otherThing") |]
                                    )
                                ,
                                    ( Variable SortK "RuleVar"
                                    , [trm| ConfigVar:SortK{} |]
                                    )
                                ]
                             )
                         ]

runWith :: Term -> IO (Either (RewriteFailed "Rewrite") (RewriteResult Pattern))
runWith t =
    second fst <$> do
        conf <- testConf
        runNoLoggingT $ runRewriteT conf mempty (rewriteStep [] [] $ Pattern_ t)

rewritesTo :: Term -> (Text, Term) -> IO ()
t1 `rewritesTo` (lbl, t2) =
    runWith t1 @?>>= Right (RewriteFinished (Just lbl) (Just mockUniqueId) $ Pattern_ t2)

getsStuck :: Term -> IO ()
getsStuck t1 =
    runWith t1 @?>>= Right (RewriteStuck $ Pattern_ t1)

branchesTo :: Term -> [(Text, Term, Predicate, Substitution)] -> IO ()
t `branchesTo` ts =
    runWith t
        @?>>= Right
            ( RewriteBranch (Pattern_ t) $
                NE.fromList $
                    map
                        (\(lbl, t', rPred, rSubst) -> (Pattern_ t', AppliedRuleMetadata lbl mockUniqueId rPred rSubst))
                        ts
            )

failsWith :: Term -> RewriteFailed "Rewrite" -> IO ()
failsWith t err =
    runWith t @?>>= Left err

----------------------------------------
-- tests for performRewrite (iterated rewrite in IO with logging)

runRewrite :: Term -> IO (Natural, RewriteResult Term)
runRewrite t = do
    conf <- testConf
    (counter, _, res) <-
        runNoLoggingT $
            performRewrite conf $
                Pattern_ t
    pure (counter, fmap (.term) res)

aborts :: RewriteFailed "Rewrite" -> Term -> IO ()
aborts failure t = runRewrite t >>= (@?= (0, RewriteAborted failure t))

newtype Steps = Steps Natural

rewrites :: Steps -> Term -> t -> (t -> RewriteResult Term) -> IO ()
rewrites (Steps n) t t' f =
    runRewrite t >>= (@?= (n, f t'))

canRewrite :: TestTree
canRewrite =
    testGroup
        "Can rewrite"
        [ testCase "Rewrites con1 once, then aborts on function" $
            let startTerm =
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                targetTerm =
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}(   \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                remainder =
                    NE.singleton ([trm| con1{}(\dv{SomeSort{}}("thing")) |], [trm| f1{}(\dv{SomeSort{}}("thing")) |])
             in rewrites
                    (Steps 1)
                    startTerm
                    targetTerm
                    (\t -> RewriteAborted (RuleApplicationUnclear rule1 t remainder) t)
        , testCase "Rewrites con3 twice, branching on con1" $ do
            let branch1 =
                    ( [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( \dv{SomeSort{}}("somethingElse"), \dv{SomeSort{}}("somethingElse") ) ), C:SortK{}) ) |]
                    , AppliedRuleMetadata
                        "con1-f2"
                        mockUniqueId
                        (Predicate TrueBool)
                        ( Map.fromList
                            [
                                ( Variable someSort "X"
                                , [trm| \dv{SomeSort{}}("somethingElse") |]
                                )
                            ,
                                ( Variable SortK "RuleVar"
                                , [trm| C:SortK{} |]
                                )
                            ]
                        )
                    )
                branch2 =
                    ( [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}(    f1{}(   \dv{SomeSort{}}("somethingElse")                                   ) ), C:SortK{}) ) |]
                    , AppliedRuleMetadata
                        "con1-f1'"
                        mockUniqueId
                        (Predicate TrueBool)
                        ( Map.fromList
                            [
                                ( Variable someSort "X"
                                , [trm| \dv{SomeSort{}}("somethingElse") |]
                                )
                            ,
                                ( Variable SortK "RuleVar"
                                , [trm| C:SortK{} |]
                                )
                            ]
                        )
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
        , testCase "when there are no rules at all" $
            getsStuck $
                app con2 [d]
        ]

abortsOnProblems :: TestTree
abortsOnProblems =
    testGroup
        "Aborts on unexpected situations or unclear rule application"
        [ testCase "when the term index is IdxNone" $
            let term =
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( \and{SomeSort{}}( con1{}( \dv{SomeSort{}}("thing") ), con2{}( \dv{SomeSort{}}("thing") ) ) ), C:SortK{} ) ) |]
             in aborts
                    (TermIndexIsNone term)
                    term
        , testCase "Errors on wrong argument count in a symbol application" $
            runRewrite
                [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing"), \dv{SomeSort{}}("thing"), \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                >>= \case
                    (_, RewriteAborted InternalMatchError{} _) -> pure ()
                    _ -> assertFailure "success"
        , testCase "Aborts when unification is not a match" $
            let t =
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con3{}(X:SomeSort{}, \dv{SomeSort{}}("thing"))), C:SortK{}) ) |]
             in aborts
                    ( RuleApplicationUnclear
                        rule3
                        t
                        (NE.singleton ([trm| \dv{SomeSort{}}("otherThing")|], [trm| X:SomeSort{} |]))
                    )
                    t
        , testCase "Aborts when definedness is unclear" $
            let t =
                    [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}(\dv{SomeSort{}}("thing"), \dv{SomeSort{}}("thing"))), C:SortK{}) ) |]
             in aborts (DefinednessUnclear rule4 (Pattern_ t) [UndefinedSymbol "f2"]) t
        ]

newtype MaxDepth = MaxDepth Natural

supportsDepthControl :: TestTree
supportsDepthControl =
    testGroup
        "supports maximum depth control"
        [ testCase "executes normally when maxDepth > maximum expected" $
            let startTerm =
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                targetTerm =
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                remainder =
                    NE.singleton ([trm| con1{}(\dv{SomeSort{}}("thing")) |], [trm| f1{}(\dv{SomeSort{}}("thing")) |])
             in rewritesToDepth
                    (MaxDepth 42)
                    (Steps 1)
                    startTerm
                    targetTerm
                    (\t -> RewriteAborted (RuleApplicationUnclear rule1 t remainder) t)
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
                    ( [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( \dv{SomeSort{}}("somethingElse"), \dv{SomeSort{}}("somethingElse") ) ), C:SortK{}) ) |]
                    , AppliedRuleMetadata
                        "con1-f2"
                        mockUniqueId
                        (Predicate TrueBool)
                        ( Map.fromList
                            [
                                ( Variable someSort "X"
                                , [trm| \dv{SomeSort{}}("somethingElse") |]
                                )
                            ,
                                ( Variable SortK "RuleVar"
                                , [trm| C:SortK{} |]
                                )
                            ]
                        )
                    )

                branch2 =
                    ( [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}(    f1{}(   \dv{SomeSort{}}("somethingElse")                                   ) ), C:SortK{}) ) |]
                    , AppliedRuleMetadata
                        "con1-f1'"
                        mockUniqueId
                        (Predicate TrueBool)
                        ( Map.fromList
                            [
                                ( Variable someSort "X"
                                , [trm| \dv{SomeSort{}}("somethingElse") |]
                                )
                            ,
                                ( Variable SortK "RuleVar"
                                , [trm| C:SortK{} |]
                                )
                            ]
                        )
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
        conf <- testConf
        (counter, _, res) <-
            runNoLoggingT $ performRewrite conf{mbMaxDepth = Just depth} $ Pattern_ t
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
                ( const $
                    RewriteCutPoint
                        "con1-f1"
                        mockUniqueId
                        [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                )
        , testCase "ignores non-matching cut-point labels" $
            let startTerm =
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                targetTerm =
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                remainder =
                    NE.singleton ([trm| con1{}(\dv{SomeSort{}}("thing")) |], [trm| f1{}(\dv{SomeSort{}}("thing")) |])
             in rewritesToCutPoint
                    "otherLabel"
                    (Steps 1)
                    startTerm
                    targetTerm
                    (\t -> RewriteAborted (RuleApplicationUnclear rule1 t remainder) t)
        , testCase "prefers reporting branches to stopping at label in one branch" $ do
            let branch1 =
                    ( [trm| kCell{}( kseq{}( inj{AnotherSort{}, SortKItem{}}( con4{}( \dv{SomeSort{}}("somethingElse"), \dv{SomeSort{}}("somethingElse") ) ), C:SortK{}) ) |]
                    , AppliedRuleMetadata
                        "con1-f2"
                        mockUniqueId
                        (Predicate TrueBool)
                        ( Map.fromList
                            [
                                ( Variable someSort "X"
                                , [trm| \dv{SomeSort{}}("somethingElse") |]
                                )
                            ,
                                ( Variable SortK "RuleVar"
                                , [trm| C:SortK{} |]
                                )
                            ]
                        )
                    )

                branch2 =
                    ( [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}(    f1{}(   \dv{SomeSort{}}("somethingElse")                                   ) ), C:SortK{}) ) |]
                    , AppliedRuleMetadata
                        "con1-f1'"
                        mockUniqueId
                        (Predicate TrueBool)
                        ( Map.fromList
                            [
                                ( Variable someSort "X"
                                , [trm| \dv{SomeSort{}}("somethingElse") |]
                                )
                            ,
                                ( Variable SortK "RuleVar"
                                , [trm| C:SortK{} |]
                                )
                            ]
                        )
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
        conf <- testConf
        (counter, _, res) <-
            runNoLoggingT $
                performRewrite conf{cutLabels = [lbl]} $
                    Pattern_ t
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
                (RewriteTerminal "con1-f1" mockUniqueId)
        , testCase "ignores non-matching labels" $
            let startTerm =
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( con1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                targetTerm =
                    [trm| kCell{}( kseq{}( inj{SomeSort{}, SortKItem{}}( f1{}( \dv{SomeSort{}}("thing") ) ), C:SortK{}) ) |]
                remainder =
                    NE.singleton ([trm| con1{}(\dv{SomeSort{}}("thing")) |], [trm| f1{}(\dv{SomeSort{}}("thing")) |])
             in rewritesToTerminal
                    "otherLabel"
                    (Steps 1)
                    startTerm
                    targetTerm
                    (\t -> RewriteAborted (RuleApplicationUnclear rule1 t remainder) t)
        ]
  where
    rewritesToTerminal :: Text -> Steps -> Term -> t -> (t -> RewriteResult Term) -> IO ()
    rewritesToTerminal lbl (Steps n) t t' f = do
        conf <- testConf
        (counter, _, res) <-
            runNoLoggingT $ performRewrite conf{terminalLabels = [lbl]} $ Pattern_ t
        (counter, fmap (.term) res) @?= (n, f t')
