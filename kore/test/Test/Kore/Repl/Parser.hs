module Test.Kore.Repl.Parser (
    test_replParser,
) where

import Data.GraphViz qualified as Graph
import Data.HashSet (
    HashSet,
 )
import Data.HashSet qualified as HashSet
import Data.Proxy
import Data.Set qualified as Set
import Data.Text (
    Text,
 )
import Data.Text qualified as Text
import Kore.Equation.DebugEquation (
    DebugApplyEquation,
    DebugAttemptEquation,
 )
import Kore.Log qualified as Log
import Kore.Repl.Data
import Kore.Repl.Parser
import Kore.Rewrite.Timeout (
    StepTimeout (..),
 )
import Numeric.Natural
import Prelude.Kore
import Test.Kore.Repl.ParserTest
import Test.Tasty (
    TestTree,
    testGroup,
 )
import Type.Reflection (
    SomeTypeRep,
    someTypeRep,
 )

test_replParser :: [TestTree]
test_replParser =
    [ helpTests `tests` "help"
    , claimTests `tests` "claim"
    , axiomTests `tests` "axiom"
    , kaxiomTests `tests` "kaxiom"
    , proveTests `tests` "prove"
    , graphTests `tests` "graph"
    , stepTests `tests` "step"
    , selectTests `tests` "select"
    , configTests `tests` "config"
    , konfigTests `tests` "konfig"
    , destTests `tests` "dest"
    , kdestTests `tests` "kdest"
    , leafsTests `tests` "leafs"
    , precBranchTests `tests` "prec-branch"
    , childrenTests `tests` "children"
    , exitTests `tests` "exit"
    , omitTests `tests` "omit"
    , labelTests `tests` "label"
    , tryTests `tests` "try"
    , ktryTests `tests` "ktry"
    , tryFTests `tests` "tryF"
    , ktryFTests `tests` "ktryF"
    , redirectTests `tests` "redirect"
    , ruleTests `tests` "rule"
    , kruleTests `tests` "krule"
    , rulesTests `tests` "rules"
    , stepfTests `tests` "stepf"
    , clearTests `tests` "clear"
    , pipeTests `tests` "pipe"
    , pipeRedirectTests `tests` "pipe redirect"
    , saveSessionTests `tests` "save-session"
    , appendTests `tests` "append"
    , pipeAppendTests `tests` "pipe append"
    , noArgsAliasTests `tests` "no arguments alias tests"
    , tryAliasTests `tests` "try alias"
    , loadScriptTests `tests` "load file"
    , initScriptTests `testsScript` "repl script"
    , aliasesWithArgs `tests` "aliases with arguments"
    , aliasRedirectionTests `tests` "alias with redirection"
    , proofStatus `tests` "proof-status"
    , logTests `tests` "log"
    , debugAttemptEquationTests `tests` "debug-attempt-equation"
    , debugApplyEquationTests `tests` "debug-apply-equation"
    , debugEquationTests `tests` "debug-equation"
    , debugAttemptRewriteTests `tests` "debug-attempt-rewrite"
    , debugApplyRewriteTests `tests` "debug-apply-rewrite"
    , debugRewriteTests `tests` "debug-rewrite"
    , stepTimeoutTests `tests` "set-step-timeout"
    , showStepTimeTests `tests` "show-step-time"
    , movingAverageTests `tests` "moving-average"
    ]

tests :: [ParserTest ReplCommand] -> String -> TestTree
tests ts pname =
    testGroup
        ("REPL.Parser." <> pname)
        . parseTree commandParser
        $ ts

testsScript :: [ParserTest [ReplCommand]] -> String -> TestTree
testsScript ts pname =
    testGroup
        ("REPL.Parser." <> pname)
        . parseTree scriptParser
        $ ts

helpTests :: [ParserTest ReplCommand]
helpTests =
    [ "help" `parsesTo_` Help
    , "help " `parsesTo_` Help
    ]

proofStatus :: [ParserTest ReplCommand]
proofStatus =
    [ "proof-status" `parsesTo_` ProofStatus
    , "proof-status " `parsesTo_` ProofStatus
    ]

claimTests :: [ParserTest ReplCommand]
claimTests =
    [ "claim 0" `parsesTo_` ShowClaim (Just . Left . ClaimIndex $ 0)
    , "claim 0 " `parsesTo_` ShowClaim (Just . Left . ClaimIndex $ 0)
    , "claim 5" `parsesTo_` ShowClaim (Just . Left . ClaimIndex $ 5)
    , "claim lbl" `parsesTo_` ShowClaim (Just . Right . RuleName $ "lbl")
    , "claim \"my lbl\" " `parsesTo_` ShowClaim (Just . Right . RuleName $ "my lbl")
    , "claim" `parsesTo_` ShowClaim Nothing
    ]

axiomTests :: [ParserTest ReplCommand]
axiomTests =
    [ "axiom 0" `parsesTo_` ShowAxiom (Left . AxiomIndex $ 0)
    , "axiom 0 " `parsesTo_` ShowAxiom (Left . AxiomIndex $ 0)
    , "axiom 5" `parsesTo_` ShowAxiom (Left . AxiomIndex $ 5)
    , "axiom lbl" `parsesTo_` ShowAxiom (Right . RuleName $ "lbl")
    , "axiom \"my lbl\" " `parsesTo_` ShowAxiom (Right . RuleName $ "my lbl")
    , "axiom" `fails` ()
    ]

kaxiomTests :: [ParserTest ReplCommand]
kaxiomTests =
    [ "kaxiom 0" `parsesTo_` ShowKAxiom (Left . AxiomIndex $ 0)
    , "kaxiom 0 " `parsesTo_` ShowKAxiom (Left . AxiomIndex $ 0)
    , "kaxiom 5" `parsesTo_` ShowKAxiom (Left . AxiomIndex $ 5)
    , "kaxiom lbl" `parsesTo_` ShowKAxiom (Right . RuleName $ "lbl")
    , "kaxiom \"my lbl\" " `parsesTo_` ShowKAxiom (Right . RuleName $ "my lbl")
    , "kaxiom" `fails` ()
    ]

proveTests :: [ParserTest ReplCommand]
proveTests =
    [ "prove 0" `parsesTo_` Prove (Left . ClaimIndex $ 0)
    , "prove 0 " `parsesTo_` Prove (Left . ClaimIndex $ 0)
    , "prove 5" `parsesTo_` Prove (Left . ClaimIndex $ 5)
    , "prove lbl" `parsesTo_` Prove (Right . RuleName $ "lbl")
    , "prove \"my lbl\" " `parsesTo_` Prove (Right . RuleName $ "my lbl")
    , "prove" `fails` ()
    ]

graphTests :: [ParserTest ReplCommand]
graphTests =
    [ "graph" `parsesTo_` ShowGraph Nothing Nothing Nothing
    , "graph " `parsesTo_` ShowGraph Nothing Nothing Nothing
    , "graph expanded" `parsesTo_` ShowGraph (Just Expanded) Nothing Nothing
    , "graph file" `parsesTo_` ShowGraph Nothing (Just "file") Nothing
    , "graph collapsed file" `parsesTo_` ShowGraph (Just Collapsed) (Just "file") Nothing
    , "graph file svg" `parsesTo_` ShowGraph Nothing (Just "file") (Just Graph.Svg)
    , "graph file jpeg" `parsesTo_` ShowGraph Nothing (Just "file") (Just Graph.Jpeg)
    , "graph file jpg" `parsesTo_` ShowGraph Nothing (Just "file") (Just Graph.Jpeg)
    , "graph file pdf" `parsesTo_` ShowGraph Nothing (Just "file") (Just Graph.Pdf)
    , "graph file png" `parsesTo_` ShowGraph Nothing (Just "file") (Just Graph.Png)
    , "graph expanded file svg" `parsesTo_` ShowGraph (Just Expanded) (Just "file") (Just Graph.Svg)
    , "graph \"f ile\"" `parsesTo_` ShowGraph Nothing (Just "f ile") Nothing
    , "graph \"f ile\" jpg" `parsesTo_` ShowGraph Nothing (Just "f ile") (Just Graph.Jpeg)
    , "graph expanded \"f ile\" jpg" `parsesTo_` ShowGraph (Just Expanded) (Just "f ile") (Just Graph.Jpeg)
    , "graph f ile" `fails` ()
    ]

stepTests :: [ParserTest ReplCommand]
stepTests =
    [ "step" `parsesTo_` ProveSteps 1
    , "step " `parsesTo_` ProveSteps 1
    , "step 5" `parsesTo_` ProveSteps 5
    , "step 5 " `parsesTo_` ProveSteps 5
    , "step -5" `fails` ()
    ]

stepfTests :: [ParserTest ReplCommand]
stepfTests =
    [ "stepf" `parsesTo_` ProveStepsF 1
    , "stepf " `parsesTo_` ProveStepsF 1
    , "stepf 5" `parsesTo_` ProveStepsF 5
    , "stepf 5 " `parsesTo_` ProveStepsF 5
    , "stepf -5" `fails` ()
    ]

selectTests :: [ParserTest ReplCommand]
selectTests =
    [ "select 5" `parsesTo_` SelectNode (ReplNode 5)
    , "select 5 " `parsesTo_` SelectNode (ReplNode 5)
    , "select -5" `fails` ()
    ]

stepTimeoutTests :: [ParserTest ReplCommand]
stepTimeoutTests =
    [ "set-step-timeout 5" `parsesTo_` SetStepTimeout (Just (StepTimeout 5))
    , "set-step-timeout 5 " `parsesTo_` SetStepTimeout (Just (StepTimeout 5))
    , "set-step-timeout" `parsesTo_` SetStepTimeout Nothing
    , "set-step-timeout -5" `fails` ()
    ]

showStepTimeTests :: [ParserTest ReplCommand]
showStepTimeTests =
    ["show-step-time" `parsesTo_` ShowStepTime]

movingAverageTests :: [ParserTest ReplCommand]
movingAverageTests =
    ["moving-average" `parsesTo_` MovingAverage]

configTests :: [ParserTest ReplCommand]
configTests =
    [ "config" `parsesTo_` ShowConfig Nothing
    , "config " `parsesTo_` ShowConfig Nothing
    , "config 5" `parsesTo_` ShowConfig (Just (ReplNode 5))
    , "config -5" `fails` ()
    , "config | > >> file" `fails` ()
    , "config | s >> " `fails` ()
    ]

konfigTests :: [ParserTest ReplCommand]
konfigTests =
    [ "konfig" `parsesTo_` ShowKonfig Nothing
    , "konfig " `parsesTo_` ShowKonfig Nothing
    , "konfig 5" `parsesTo_` ShowKonfig (Just (ReplNode 5))
    , "konfig -5" `fails` ()
    , "konfig | > >> file" `fails` ()
    , "konfig | s >> " `fails` ()
    ]

destTests :: [ParserTest ReplCommand]
destTests =
    [ "dest" `parsesTo_` ShowDest Nothing
    , "dest " `parsesTo_` ShowDest Nothing
    , "dest 5" `parsesTo_` ShowDest (Just (ReplNode 5))
    , "dest -5" `fails` ()
    , "dest | > >> file" `fails` ()
    , "dest | s >> " `fails` ()
    ]

kdestTests :: [ParserTest ReplCommand]
kdestTests =
    [ "kdest" `parsesTo_` ShowKDest Nothing
    , "kdest " `parsesTo_` ShowKDest Nothing
    , "kdest 5" `parsesTo_` ShowKDest (Just (ReplNode 5))
    , "kdest -5" `fails` ()
    , "kdest | > >> file" `fails` ()
    , "kdest | s >> " `fails` ()
    ]

omitTests :: [ParserTest ReplCommand]
omitTests =
    [ "omit" `parsesTo_` OmitCell Nothing
    , "omit " `parsesTo_` OmitCell Nothing
    , "omit   " `parsesTo_` OmitCell Nothing
    , "omit k" `parsesTo_` OmitCell (Just "k")
    , "omit k " `parsesTo_` OmitCell (Just "k")
    , "omit state " `parsesTo_` OmitCell (Just "state")
    , "omit Lbl-LT-'State-GT" `parsesTo_` OmitCell (Just "Lbl-LT-'State-GT")
    ]

leafsTests :: [ParserTest ReplCommand]
leafsTests =
    [ "leafs" `parsesTo_` ShowLeafs
    , "leafs " `parsesTo_` ShowLeafs
    ]

precBranchTests :: [ParserTest ReplCommand]
precBranchTests =
    [ "prec-branch" `parsesTo_` ShowPrecBranch Nothing
    , "prec-branch " `parsesTo_` ShowPrecBranch Nothing
    , "prec-branch 5" `parsesTo_` ShowPrecBranch (Just (ReplNode 5))
    , "prec-branch -5" `fails` ()
    ]

childrenTests :: [ParserTest ReplCommand]
childrenTests =
    [ "children" `parsesTo_` ShowChildren Nothing
    , "children " `parsesTo_` ShowChildren Nothing
    , "children 5" `parsesTo_` ShowChildren (Just (ReplNode 5))
    , "children -5" `fails` ()
    ]

labelTests :: [ParserTest ReplCommand]
labelTests =
    [ "label" `parsesTo_` Label Nothing
    , "label " `parsesTo_` Label Nothing
    , "label label" `parsesTo_` Label (Just "label")
    , "label 1ab31" `parsesTo_` Label (Just "1ab31")
    , "label +label" `parsesTo_` LabelAdd "label" Nothing
    , "label +1ab31" `parsesTo_` LabelAdd "1ab31" Nothing
    , "label +-" `parsesTo_` LabelAdd "-" Nothing
    , "label +label 5" `parsesTo_` LabelAdd "label" (Just (ReplNode 5))
    , "label +1ab31 5" `parsesTo_` LabelAdd "1ab31" (Just (ReplNode 5))
    , "label -label" `parsesTo_` LabelDel "label"
    , "label -1ab31" `parsesTo_` LabelDel "1ab31"
    ]

tryTests :: [ParserTest ReplCommand]
tryTests =
    [ "try a5" `parsesTo_` tryAxiomIndex 5
    , "try c5" `parsesTo_` tryClaimIndex 5
    , "try lbl" `parsesTo_` tryRuleName "lbl"
    , "try \"my lbl\" " `parsesTo_` tryRuleName "my lbl"
    , "try albl" `parsesTo_` tryRuleName "albl"
    , "try clbl" `parsesTo_` tryRuleName "clbl"
    , "try" `fails` ()
    ]

ktryTests :: [ParserTest ReplCommand]
ktryTests =
    [ "ktry a5" `parsesTo_` tryKAxiomIndex 5
    , "ktry c5" `parsesTo_` tryKClaimIndex 5
    , "ktry lbl" `parsesTo_` tryKRuleName "lbl"
    , "ktry \"my lbl\" " `parsesTo_` tryKRuleName "my lbl"
    , "ktry albl" `parsesTo_` tryKRuleName "albl"
    , "ktry clbl" `parsesTo_` tryKRuleName "clbl"
    , "ktry" `fails` ()
    ]

tryFTests :: [ParserTest ReplCommand]
tryFTests =
    [ "tryf a5" `parsesTo_` tryFAxiomIndex 5
    , "tryf c5" `parsesTo_` tryFClaimIndex 5
    , "tryf lbl" `parsesTo_` tryFRuleName "lbl"
    , "tryf \"my lbl\" " `parsesTo_` tryFRuleName "my lbl"
    , "tryf albl" `parsesTo_` tryFRuleName "albl"
    , "tryf clbl" `parsesTo_` tryFRuleName "clbl"
    , "tryf" `fails` ()
    ]

ktryFTests :: [ParserTest ReplCommand]
ktryFTests =
    [ "ktryf a5" `parsesTo_` tryFKAxiomIndex 5
    , "ktryf c5" `parsesTo_` tryFKClaimIndex 5
    , "ktryf lbl" `parsesTo_` tryFKRuleName "lbl"
    , "ktryf \"my lbl\" " `parsesTo_` tryFKRuleName "my lbl"
    , "ktryf albl" `parsesTo_` tryFKRuleName "albl"
    , "ktryf clbl" `parsesTo_` tryFKRuleName "clbl"
    , "ktryf" `fails` ()
    ]

tryAxiomIndex :: Int -> ReplCommand
tryAxiomIndex = Try . ByIndex . Left . AxiomIndex

tryKAxiomIndex :: Int -> ReplCommand
tryKAxiomIndex = KTry . ByIndex . Left . AxiomIndex

tryClaimIndex :: Int -> ReplCommand
tryClaimIndex = Try . ByIndex . Right . ClaimIndex

tryKClaimIndex :: Int -> ReplCommand
tryKClaimIndex = KTry . ByIndex . Right . ClaimIndex

tryRuleName :: String -> ReplCommand
tryRuleName = Try . ByName . RuleName

tryKRuleName :: String -> ReplCommand
tryKRuleName = KTry . ByName . RuleName

tryFAxiomIndex :: Int -> ReplCommand
tryFAxiomIndex = TryF . ByIndex . Left . AxiomIndex

tryFKAxiomIndex :: Int -> ReplCommand
tryFKAxiomIndex = KTryF . ByIndex . Left . AxiomIndex

tryFClaimIndex :: Int -> ReplCommand
tryFClaimIndex = TryF . ByIndex . Right . ClaimIndex

tryFKClaimIndex :: Int -> ReplCommand
tryFKClaimIndex = KTryF . ByIndex . Right . ClaimIndex

tryFRuleName :: String -> ReplCommand
tryFRuleName = TryF . ByName . RuleName

tryFKRuleName :: String -> ReplCommand
tryFKRuleName = KTryF . ByName . RuleName

exitTests :: [ParserTest ReplCommand]
exitTests =
    [ "exit" `parsesTo_` Exit
    , "exit " `parsesTo_` Exit
    ]

redirectTests :: [ParserTest ReplCommand]
redirectTests =
    [ "config > file" `parsesTo_` redirectConfig Nothing "file"
    , "config 5 > file" `parsesTo_` redirectConfig (Just $ ReplNode 5) "file"
    , "config 5 > file" `parsesTo_` redirectConfig (Just $ ReplNode 5) "file"
    , "claim 3 > cf" `parsesTo_` redirectClaim (Just . Left . ClaimIndex $ 3) "cf"
    , "claim 3 > \"c f\"" `parsesTo_` redirectClaim (Just . Left . ClaimIndex $ 3) "c f"
    , "claim > cf" `parsesTo_` redirectClaim Nothing "cf"
    , "claim > \"c f\"" `parsesTo_` redirectClaim Nothing "c f"
    , "config 5 > " `fails` ()
    ]
  where
    redirectConfig maybeNode file = Redirect (ShowConfig maybeNode) file
    redirectClaim maybeClaim file = Redirect (ShowClaim maybeClaim) file

pipeTests :: [ParserTest ReplCommand]
pipeTests =
    [ "config | script" `parsesTo_` pipeConfig Nothing "script" []
    , "config 5 | script" `parsesTo_` pipeConfig (Just (ReplNode 5)) "script" []
    , "config 5 | script \"arg1\" \"arg2\"" `parsesTo_` pipeConfig (Just (ReplNode 5)) "script" ["arg1", "arg2"]
    , "step 5 | script" `parsesTo_` pipeStep 5 "script" []
    , "step 5 | \"s c ri p t\"" `parsesTo_` pipeStep 5 "s c ri p t" []
    , "claim | exe a1 a2" `parsesTo_` pipeClaim Nothing "exe" ["a1", "a2"]
    , "claim | \"e x e\" a1 \"a2\"" `parsesTo_` pipeClaim Nothing "e x e" ["a1", "a2"]
    , "config 5 | " `fails` ()
    ]
  where
    pipeConfig ::
        Maybe ReplNode ->
        String ->
        [String] ->
        ReplCommand
    pipeConfig mrnode s xs =
        Pipe (ShowConfig mrnode) s xs
    pipeStep ::
        Natural ->
        String ->
        [String] ->
        ReplCommand
    pipeStep n s xs =
        Pipe (ProveSteps n) s xs
    pipeClaim ::
        Maybe (Either ClaimIndex RuleName) ->
        String ->
        [String] ->
        ReplCommand
    pipeClaim maybeClaim exe opts =
        Pipe (ShowClaim maybeClaim) exe opts

pipeRedirectTests :: [ParserTest ReplCommand]
pipeRedirectTests =
    [ "config | script > file"
        `parsesTo_` pipeRedirectConfig Nothing "script" [] "file"
    , "config | \"s cript\" \"arg 1\" arg2 > \"f ile\""
        `parsesTo_` pipeRedirectConfig Nothing "s cript" ["arg 1", "arg2"] "f ile"
    , "config 5 | script \"a r g 1\" arg2 > file"
        `parsesTo_` pipeRedirectConfig (Just (ReplNode 5)) "script" ["a r g 1", "arg2"] "file"
    ]

pipeRedirectConfig ::
    Maybe ReplNode ->
    String ->
    [String] ->
    String ->
    ReplCommand
pipeRedirectConfig mrnode s xs file =
    Redirect (Pipe (ShowConfig mrnode) s xs) file

appendTests :: [ParserTest ReplCommand]
appendTests =
    [ "config >> file" `parsesTo_` AppendTo (ShowConfig Nothing) "file"
    , "config >> \"f i l e\"" `parsesTo_` AppendTo (ShowConfig Nothing) "f i l e"
    , "config >> " `fails` ()
    ]

pipeAppendTests :: [ParserTest ReplCommand]
pipeAppendTests =
    [ "config | script >> file"
        `parsesTo_` pipeAppendConfig Nothing "script" [] "file"
    , "config 5 | \"sc ript\" arg1 \"a rg\" >> \"f ile\""
        `parsesTo_` pipeAppendConfig (Just (ReplNode 5)) "sc ript" ["arg1", "a rg"] "f ile"
    ]

pipeAppendConfig ::
    Maybe ReplNode ->
    String ->
    [String] ->
    String ->
    ReplCommand
pipeAppendConfig mrnode s xs file =
    AppendTo (Pipe (ShowConfig mrnode) s xs) file

ruleTests :: [ParserTest ReplCommand]
ruleTests =
    [ "rule" `parsesTo_` ShowRule Nothing
    , "rule " `parsesTo_` ShowRule Nothing
    , "rule 5" `parsesTo_` ShowRule (Just (ReplNode 5))
    , "rule 5 " `parsesTo_` ShowRule (Just (ReplNode 5))
    , "rule -5" `fails` ()
    ]

kruleTests :: [ParserTest ReplCommand]
kruleTests =
    [ "krule" `parsesTo_` ShowKRule Nothing
    , "krule " `parsesTo_` ShowKRule Nothing
    , "krule 5" `parsesTo_` ShowKRule (Just (ReplNode 5))
    , "krule 5 " `parsesTo_` ShowKRule (Just (ReplNode 5))
    , "krule -5" `fails` ()
    ]

rulesTests :: [ParserTest ReplCommand]
rulesTests =
    [ "rules 1 9" `parsesTo_` ShowRules (ReplNode 1, ReplNode 9)
    , "rules 1 97" `parsesTo_` ShowRules (ReplNode 1, ReplNode 97)
    , "rules  1 97" `parsesTo_` ShowRules (ReplNode 1, ReplNode 97)
    , "rules 1  97 " `parsesTo_` ShowRules (ReplNode 1, ReplNode 97)
    , "rules 97 105" `parsesTo_` ShowRules (ReplNode 97, ReplNode 105)
    , "rules" `fails` ()
    , "rules " `fails` ()
    , "rules 13" `fails` ()
    , "rules -13" `fails` ()
    ]

clearTests :: [ParserTest ReplCommand]
clearTests =
    [ "clear" `parsesTo_` Clear Nothing
    , "clear " `parsesTo_` Clear Nothing
    , "clear 5" `parsesTo_` Clear (Just (ReplNode 5))
    , "clear 5 " `parsesTo_` Clear (Just (ReplNode 5))
    , "clear -5" `fails` ()
    ]

saveSessionTests :: [ParserTest ReplCommand]
saveSessionTests =
    [ "save-session file" `parsesTo_` SaveSession "file"
    , "save-session file " `parsesTo_` SaveSession "file"
    , "save-session" `fails` ()
    ]

noArgsAliasTests :: [ParserTest ReplCommand]
noArgsAliasTests =
    [ "alias a = help" `parsesTo_` alias "help"
    , "alias a = config 10" `parsesTo_` alias "config 10"
    , "alias a = config 10 | c" `parsesTo_` alias "config 10 | c"
    , "alias a = config 10 > f" `parsesTo_` alias "config 10 > f"
    , "alias a = config 10 | c > f" `parsesTo_` alias "config 10 | c > f"
    ]
  where
    alias = Alias . AliasDefinition "a" []

tryAliasTests :: [ParserTest ReplCommand]
tryAliasTests =
    [ "whatever" `parsesTo_` tryAlias "whatever" []
    , "c 1 \"a b\"" `parsesTo_` tryAlias "c" [str "1", quoted "a b"]
    ]
  where
    tryAlias name = TryAlias . ReplAlias name
    str = SimpleArgument
    quoted = QuotedArgument

aliasesWithArgs :: [ParserTest ReplCommand]
aliasesWithArgs =
    [ "alias s n = step n" `parsesTo_` alias "s" ["n"] "step n"
    , "alias s = step 1 > \"a b\"" `parsesTo_` alias "s" [] "step 1 > \"a b\""
    , "alias c n s = config n | echo \"hello world\" > s"
        `parsesTo_` alias "c" ["n", "s"] "config n | echo \"hello world\" > s"
    ]
  where
    alias name arguments command =
        Alias $ AliasDefinition{name, arguments, command}

aliasRedirectionTests :: [ParserTest ReplCommand]
aliasRedirectionTests =
    [ parsesTo_
        "myAlias > file"
        ( Redirect
            ( TryAlias
                ReplAlias{name = "myAlias", arguments = []}
            )
            "file"
        )
    , parsesTo_
        "myAlias >> file"
        ( AppendTo
            ( TryAlias
                ReplAlias{name = "myAlias", arguments = []}
            )
            "file"
        )
    , parsesTo_
        "myAlias | script > file"
        ( Redirect
            ( Pipe
                ( TryAlias
                    ReplAlias{name = "myAlias", arguments = []}
                )
                "script"
                []
            )
            "file"
        )
    ]

loadScriptTests :: [ParserTest ReplCommand]
loadScriptTests =
    [ "load file" `parsesTo_` LoadScript "file"
    , "load file " `parsesTo_` LoadScript "file"
    , "load \"f ile\"" `parsesTo_` LoadScript "f ile"
    , "load" `fails` ()
    ]

initScriptTests :: [ParserTest [ReplCommand]]
initScriptTests =
    [ let script1 =
            "// comment\n\
            \step 5    \n\n\n\
            \try a3\n\
            \/* multi\n\
            \line\n\
            \comment */\n\
            \stepf    10\n\
            \config   5 | grep predicate > file\n\
            \// comment\n\
            \select    9    \n"
          commands1 =
            [ ProveSteps 5
            , tryAxiomIndex 3
            , ProveStepsF 10
            , pipeRedirectConfig (Just (ReplNode 5)) "grep" ["predicate"] "file"
            , SelectNode (ReplNode 9)
            ]
       in script1 `parsesTo_` commands1
    ]

logTests :: [ParserTest ReplCommand]
logTests =
    [ "log debug [] stderr"
        `parsesTo_` Log
            GeneralLogOptions
                { logLevel = Log.Debug
                , logType = Log.LogStdErr
                , logFormat = Log.Standard
                , timestampsSwitch = Log.TimestampsEnable
                , logEntries = mempty
                }
    , "log [] stderr"
        `parsesTo_` Log
            GeneralLogOptions
                { logLevel = Log.Warning
                , logType = Log.LogStdErr
                , logFormat = Log.Standard
                , timestampsSwitch = Log.TimestampsEnable
                , logEntries = mempty
                }
    , "log [DebugAttemptEquation] stderr"
        `parsesTo_` Log
            GeneralLogOptions
                { logLevel = Log.Warning
                , logType = Log.LogStdErr
                , logFormat = Log.Standard
                , logEntries = Set.singleton debugAttemptEquationType
                , timestampsSwitch = Log.TimestampsEnable
                }
    , "log error [DebugAttemptEquation] stderr"
        `parsesTo_` Log
            GeneralLogOptions
                { logLevel = Log.Error
                , logType = Log.LogStdErr
                , logFormat = Log.Standard
                , logEntries = Set.singleton debugAttemptEquationType
                , timestampsSwitch = Log.TimestampsEnable
                }
    , "log info [ DebugAttemptEquation,  DebugApplyEquation ] file \"f s\""
        `parsesTo_` Log
            GeneralLogOptions
                { logLevel = Log.Info
                , logType = Log.LogFileText "f s"
                , logFormat = Log.Standard
                , logEntries =
                    Set.fromList
                        [debugAttemptEquationType, debugApplyEquationType]
                , timestampsSwitch = Log.TimestampsEnable
                }
    , "log info [ DebugAttemptEquation   DebugApplyEquation ] file \"f s\""
        `parsesTo_` Log
            GeneralLogOptions
                { logLevel = Log.Info
                , logType = Log.LogFileText "f s"
                , logFormat = Log.Standard
                , logEntries =
                    Set.fromList
                        [debugAttemptEquationType, debugApplyEquationType]
                , timestampsSwitch = Log.TimestampsEnable
                }
    , "log oneline [] stderr"
        `parsesTo_` Log
            GeneralLogOptions
                { logLevel = Log.Warning
                , logType = Log.LogStdErr
                , logFormat = Log.OneLine
                , logEntries = Set.empty
                , timestampsSwitch = Log.TimestampsEnable
                }
    , "log standard [] stderr"
        `parsesTo_` Log
            GeneralLogOptions
                { logLevel = Log.Warning
                , logType = Log.LogStdErr
                , logFormat = Log.Standard
                , logEntries = Set.empty
                , timestampsSwitch = Log.TimestampsEnable
                }
    , "log [] stderr enable-log-timestamps"
        `parsesTo_` Log
            GeneralLogOptions
                { logLevel = Log.Warning
                , logType = Log.LogStdErr
                , logFormat = Log.Standard
                , logEntries = Set.empty
                , timestampsSwitch = Log.TimestampsEnable
                }
    , "log [] stderr disable-log-timestamps"
        `parsesTo_` Log
            GeneralLogOptions
                { logLevel = Log.Warning
                , logType = Log.LogStdErr
                , logFormat = Log.Standard
                , logEntries = Set.empty
                , timestampsSwitch = Log.TimestampsDisable
                }
    ]

debugAttemptEquationTests :: [ParserTest ReplCommand]
debugAttemptEquationTests =
    [ "debug-attempt-equation"
        `parsesTo_` DebugAttemptEquation
            Log.DebugAttemptEquationOptions
                { Log.selected =
                    fromList
                        []
                }
    , Text.pack ("debug-attempt-equation " <> totalBalanceSymbolId)
        `parsesTo_` DebugAttemptEquation
            Log.DebugAttemptEquationOptions
                { Log.selected =
                    fromList
                        [totalBalanceSymbolId]
                }
    , Text.pack ("debug-attempt-equation " <> totalBalanceSymbolId <> " " <> plusSymbolId)
        `parsesTo_` DebugAttemptEquation
            Log.DebugAttemptEquationOptions
                { Log.selected =
                    fromList
                        [totalBalanceSymbolId, plusSymbolId]
                }
    , "debug-attempt-equation label1 label2"
        `parsesTo_` DebugAttemptEquation
            Log.DebugAttemptEquationOptions
                { Log.selected =
                    fromList
                        ["label1", "label2"]
                }
    , "debug-attempt-equation MODULE.label1 MODULE.label2"
        `parsesTo_` DebugAttemptEquation
            Log.DebugAttemptEquationOptions
                { Log.selected =
                    fromList
                        ["MODULE.label1", "MODULE.label2"]
                }
    ]

debugApplyEquationTests :: [ParserTest ReplCommand]
debugApplyEquationTests =
    [ "debug-apply-equation"
        `parsesTo_` DebugApplyEquation
            Log.DebugApplyEquationOptions
                { Log.selected =
                    fromList
                        []
                }
    , Text.pack ("debug-apply-equation " <> totalBalanceSymbolId)
        `parsesTo_` DebugApplyEquation
            Log.DebugApplyEquationOptions
                { Log.selected =
                    fromList
                        [totalBalanceSymbolId]
                }
    , Text.pack ("debug-apply-equation " <> totalBalanceSymbolId <> " " <> plusSymbolId)
        `parsesTo_` DebugApplyEquation
            Log.DebugApplyEquationOptions
                { Log.selected =
                    fromList
                        [totalBalanceSymbolId, plusSymbolId]
                }
    , "debug-apply-equation label1 label2"
        `parsesTo_` DebugApplyEquation
            Log.DebugApplyEquationOptions
                { Log.selected =
                    fromList
                        ["label1", "label2"]
                }
    , "debug-apply-equation MODULE.label1 MODULE.label2"
        `parsesTo_` DebugApplyEquation
            Log.DebugApplyEquationOptions
                { Log.selected =
                    fromList
                        ["MODULE.label1", "MODULE.label2"]
                }
    ]

debugEquationTests :: [ParserTest ReplCommand]
debugEquationTests =
    [ "debug-equation"
        `parsesTo_` DebugEquation
            Log.DebugEquationOptions
                { Log.selected =
                    fromList
                        []
                }
    , Text.pack ("debug-equation " <> totalBalanceSymbolId)
        `parsesTo_` DebugEquation
            Log.DebugEquationOptions
                { Log.selected =
                    fromList
                        [totalBalanceSymbolId]
                }
    , Text.pack ("debug-equation " <> totalBalanceSymbolId <> " " <> plusSymbolId)
        `parsesTo_` DebugEquation
            Log.DebugEquationOptions
                { Log.selected =
                    fromList
                        [totalBalanceSymbolId, plusSymbolId]
                }
    , "debug-equation label1 label2"
        `parsesTo_` DebugEquation
            Log.DebugEquationOptions
                { Log.selected =
                    fromList
                        ["label1", "label2"]
                }
    , "debug-equation MODULE.label1 MODULE.label2"
        `parsesTo_` DebugEquation
            Log.DebugEquationOptions
                { Log.selected =
                    fromList
                        ["MODULE.label1", "MODULE.label2"]
                }
    ]

debugAttemptRewriteTests :: [ParserTest ReplCommand]
debugAttemptRewriteTests =
    [ "debug-attempt-rewrite"
        `parsesTo_` DebugAttemptRewrite
            Log.DebugAttemptRewriteOptions
                { Log.selected =
                    fromList
                        []
                }
    , Text.pack ("debug-attempt-rewrite " <> totalBalanceSymbolId)
        `parsesTo_` DebugAttemptRewrite
            Log.DebugAttemptRewriteOptions
                { Log.selected =
                    fromList
                        [totalBalanceSymbolId]
                }
    , Text.pack ("debug-attempt-rewrite " <> totalBalanceSymbolId <> " " <> plusSymbolId)
        `parsesTo_` DebugAttemptRewrite
            Log.DebugAttemptRewriteOptions
                { Log.selected =
                    fromList
                        [totalBalanceSymbolId, plusSymbolId]
                }
    , "debug-attempt-rewrite label1 label2"
        `parsesTo_` DebugAttemptRewrite
            Log.DebugAttemptRewriteOptions
                { Log.selected =
                    fromList
                        ["label1", "label2"]
                }
    , "debug-attempt-rewrite MODULE.label1 MODULE.label2"
        `parsesTo_` DebugAttemptRewrite
            Log.DebugAttemptRewriteOptions
                { Log.selected =
                    fromList
                        ["MODULE.label1", "MODULE.label2"]
                }
    ]

debugApplyRewriteTests :: [ParserTest ReplCommand]
debugApplyRewriteTests =
    [ "debug-apply-rewrite"
        `parsesTo_` DebugApplyRewrite
            Log.DebugApplyRewriteOptions
                { Log.selected =
                    fromList
                        []
                }
    , Text.pack ("debug-apply-rewrite " <> totalBalanceSymbolId)
        `parsesTo_` DebugApplyRewrite
            Log.DebugApplyRewriteOptions
                { Log.selected =
                    fromList
                        [totalBalanceSymbolId]
                }
    , Text.pack ("debug-apply-rewrite " <> totalBalanceSymbolId <> " " <> plusSymbolId)
        `parsesTo_` DebugApplyRewrite
            Log.DebugApplyRewriteOptions
                { Log.selected =
                    fromList
                        [totalBalanceSymbolId, plusSymbolId]
                }
    , "debug-apply-rewrite label1 label2"
        `parsesTo_` DebugApplyRewrite
            Log.DebugApplyRewriteOptions
                { Log.selected =
                    fromList
                        ["label1", "label2"]
                }
    , "debug-apply-rewrite MODULE.label1 MODULE.label2"
        `parsesTo_` DebugApplyRewrite
            Log.DebugApplyRewriteOptions
                { Log.selected =
                    fromList
                        ["MODULE.label1", "MODULE.label2"]
                }
    ]

debugRewriteTests :: [ParserTest ReplCommand]
debugRewriteTests =
    [ "debug-rewrite"
        `parsesTo_` DebugRewrite
            Log.DebugRewriteOptions
                { Log.selected =
                    fromList
                        []
                }
    , Text.pack ("debug-rewrite" <> totalBalanceSymbolId)
        `parsesTo_` DebugRewrite
            Log.DebugRewriteOptions
                { Log.selected =
                    fromList
                        [totalBalanceSymbolId]
                }
    , Text.pack ("debug-rewrite" <> totalBalanceSymbolId <> " " <> plusSymbolId)
        `parsesTo_` DebugRewrite
            Log.DebugRewriteOptions
                { Log.selected =
                    fromList
                        [totalBalanceSymbolId, plusSymbolId]
                }
    , "debug-rewrite label1 label2"
        `parsesTo_` DebugRewrite
            Log.DebugRewriteOptions
                { Log.selected =
                    fromList
                        ["label1", "label2"]
                }
    , "debug-rewrite MODULE.label1 MODULE.label2"
        `parsesTo_` DebugRewrite
            Log.DebugRewriteOptions
                { Log.selected =
                    fromList
                        ["MODULE.label1", "MODULE.label2"]
                }
    ]

fromList :: [String] -> HashSet Text
fromList = HashSet.fromList . fmap Text.pack

totalBalanceSymbolId, plusSymbolId :: String
totalBalanceSymbolId =
    "Lbltotal'Unds'balance'LParUndsRParUnds'WITH-CONFIG'Unds'Int'Unds'AccountId"
plusSymbolId =
    "Lbl'UndsPlusUndsUnds'IMP-SYNTAX'Unds'AExp'Unds'AExp'Unds'AExp"

debugAttemptEquationType, debugApplyEquationType :: SomeTypeRep
debugAttemptEquationType = someTypeRep (Proxy @DebugAttemptEquation)
debugApplyEquationType = someTypeRep (Proxy @DebugApplyEquation)
