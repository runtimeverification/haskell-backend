module Test.Kore.Repl.Parser
    ( test_replParser
    ) where

import Numeric.Natural
import Test.Tasty
    ( TestTree
    , testGroup
    )

import qualified Kore.Logger as Logger
import Kore.Repl.Data
import Kore.Repl.Parser

import Test.Kore.Parser

test_replParser :: [TestTree]
test_replParser =
    [ helpTests         `tests`       "help"
    , claimTests        `tests`       "claim"
    , axiomTests        `tests`       "axiom"
    , proveTests        `tests`       "prove"
    , graphTests        `tests`       "graph"
    , stepTests         `tests`       "step"
    , selectTests       `tests`       "select"
    , configTests       `tests`       "config"
    , leafsTests        `tests`       "leafs"
    , precBranchTests   `tests`       "prec-branch"
    , childrenTests     `tests`       "children"
    , exitTests         `tests`       "exit"
    , omitTests         `tests`       "omit"
    , labelTests        `tests`       "label"
    , tryTests          `tests`       "try"
    , tryFTests         `tests`       "tryF"
    , redirectTests     `tests`       "redirect"
    , ruleTests         `tests`       "rule"
    , stepfTests        `tests`       "stepf"
    , clearTests        `tests`       "clear"
    , pipeTests         `tests`       "pipe"
    , pipeRedirectTests `tests`       "pipe redirect"
    , saveSessionTests  `tests`       "save-session"
    , appendTests       `tests`       "append"
    , pipeAppendTests   `tests`       "pipe append"
    , noArgsAliasTests  `tests`       "no arguments alias tests"
    , tryAliasTests     `tests`       "try alias"
    , loadScriptTests   `tests`       "load file"
    , initScriptTests   `testsScript` "repl script"
    , aliasesWithArgs   `tests`       "aliases with arguments"
    , proofStatus       `tests`       "proof-status"
    , logTests          `tests`       "log"
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
    [ "help"  `parsesTo_` Help
    , "help " `parsesTo_` Help
    ]

proofStatus :: [ParserTest ReplCommand]
proofStatus =
    [ "proof-status"  `parsesTo_` ProofStatus
    , "proof-status " `parsesTo_` ProofStatus
    ]

claimTests :: [ParserTest ReplCommand]
claimTests =
    [ "claim 0"            `parsesTo_` ShowClaim (Just . Left . ClaimIndex $ 0)
    , "claim 0 "           `parsesTo_` ShowClaim (Just . Left . ClaimIndex $ 0)
    , "claim 5"            `parsesTo_` ShowClaim (Just . Left . ClaimIndex $ 5)
    , "claim lbl"          `parsesTo_` ShowClaim (Just . Right . RuleName $ "lbl")
    , "claim \"my lbl\" "  `parsesTo_` ShowClaim (Just . Right . RuleName $ "my lbl")
    , "claim"              `parsesTo_` ShowClaim Nothing
    ]

axiomTests :: [ParserTest ReplCommand]
axiomTests =
    [ "axiom 0"            `parsesTo_` ShowAxiom (Left . AxiomIndex $ 0)
    , "axiom 0 "           `parsesTo_` ShowAxiom (Left . AxiomIndex $ 0)
    , "axiom 5"            `parsesTo_` ShowAxiom (Left . AxiomIndex $ 5)
    , "axiom lbl"          `parsesTo_` ShowAxiom (Right . RuleName$ "lbl")
    , "axiom \"my lbl\" "  `parsesTo_` ShowAxiom (Right . RuleName $ "my lbl")
    , "axiom"              `fails`     ()
    ]

proveTests :: [ParserTest ReplCommand]
proveTests =
    [ "prove 0"  `parsesTo_` Prove (Left . ClaimIndex $ 0)
    , "prove 0 " `parsesTo_` Prove (Left . ClaimIndex $ 0)
    , "prove 5"  `parsesTo_` Prove (Left . ClaimIndex $ 5)
    , "prove lbl"          `parsesTo_` Prove (Right . RuleName $ "lbl")
    , "prove \"my lbl\" "  `parsesTo_` Prove (Right . RuleName $ "my lbl")
    , "prove"    `fails`     ()
    ]

graphTests :: [ParserTest ReplCommand]
graphTests =
    [ "graph"           `parsesTo_` ShowGraph Nothing
    , "graph "          `parsesTo_` ShowGraph Nothing
    , "graph file"      `parsesTo_` ShowGraph (Just "file")
    , "graph \"f ile\"" `parsesTo_` ShowGraph (Just "f ile")
    , "graph f ile"     `fails`     ()
    ]

stepTests :: [ParserTest ReplCommand]
stepTests =
    [ "step"    `parsesTo_` ProveSteps 1
    , "step "   `parsesTo_` ProveSteps 1
    , "step 5"  `parsesTo_` ProveSteps 5
    , "step 5 " `parsesTo_` ProveSteps 5
    , "step -5" `fails`     ()
    ]

stepfTests :: [ParserTest ReplCommand]
stepfTests =
    [ "stepf"    `parsesTo_` ProveStepsF 1
    , "stepf "   `parsesTo_` ProveStepsF 1
    , "stepf 5"  `parsesTo_` ProveStepsF 5
    , "stepf 5 " `parsesTo_` ProveStepsF 5
    , "stepf -5" `fails`     ()
    ]

selectTests :: [ParserTest ReplCommand]
selectTests =
    [ "select 5"  `parsesTo_` SelectNode (ReplNode 5)
    , "select 5 " `parsesTo_` SelectNode (ReplNode 5)
    , "select -5" `fails`     ()
    ]

configTests :: [ParserTest ReplCommand]
configTests =
    [ "config"             `parsesTo_` ShowConfig Nothing
    , "config "            `parsesTo_` ShowConfig Nothing
    , "config 5"           `parsesTo_` ShowConfig (Just (ReplNode 5))
    , "config -5"          `fails`     ()
    , "config | > >> file" `fails`     ()
    , "config | s >> "     `fails`     ()
    ]

omitTests :: [ParserTest ReplCommand]
omitTests =
    [ "omit"                  `parsesTo_` OmitCell Nothing
    , "omit "                 `parsesTo_` OmitCell Nothing
    , "omit   "               `parsesTo_` OmitCell Nothing
    , "omit k"                `parsesTo_` OmitCell (Just "k")
    , "omit k "               `parsesTo_` OmitCell (Just "k")
    , "omit state "           `parsesTo_` OmitCell (Just "state")
    , "omit Lbl-LT-'State-GT" `parsesTo_` OmitCell (Just "Lbl-LT-'State-GT")
    ]

leafsTests :: [ParserTest ReplCommand]
leafsTests =
    [ "leafs"  `parsesTo_` ShowLeafs
    , "leafs " `parsesTo_` ShowLeafs
    ]

precBranchTests :: [ParserTest ReplCommand]
precBranchTests =
    [ "prec-branch"    `parsesTo_` ShowPrecBranch Nothing
    , "prec-branch "   `parsesTo_` ShowPrecBranch Nothing
    , "prec-branch 5"  `parsesTo_` ShowPrecBranch (Just (ReplNode 5))
    , "prec-branch -5" `fails`     ()
    ]

childrenTests :: [ParserTest ReplCommand]
childrenTests =
    [ "children"    `parsesTo_` ShowChildren Nothing
    , "children "   `parsesTo_` ShowChildren Nothing
    , "children 5"  `parsesTo_` ShowChildren (Just (ReplNode 5))
    , "children -5" `fails`     ()
    ]

labelTests :: [ParserTest ReplCommand]
labelTests =
    [ "label"           `parsesTo_` Label Nothing
    , "label "          `parsesTo_` Label Nothing
    , "label label"     `parsesTo_` Label (Just "label")
    , "label 1ab31"     `parsesTo_` Label (Just "1ab31")
    , "label +label"    `parsesTo_` LabelAdd "label" Nothing
    , "label +1ab31"    `parsesTo_` LabelAdd "1ab31" Nothing
    , "label +-"        `parsesTo_` LabelAdd "-" Nothing
    , "label +label 5"  `parsesTo_` LabelAdd "label" (Just (ReplNode 5))
    , "label +1ab31 5"  `parsesTo_` LabelAdd "1ab31" (Just (ReplNode 5))
    , "label -label"    `parsesTo_` LabelDel "label"
    , "label -1ab31"    `parsesTo_` LabelDel "1ab31"
    ]

tryTests :: [ParserTest ReplCommand]
tryTests =
    [ "try a5"            `parsesTo_` tryAxiomIndex 5
    , "try c5"            `parsesTo_` tryClaimIndex 5
    , "try lbl"           `parsesTo_` tryRuleName "lbl"
    , "try \"my lbl\" "   `parsesTo_` tryRuleName "my lbl"
    , "try albl"          `parsesTo_` tryRuleName "albl"
    , "try clbl"          `parsesTo_` tryRuleName "clbl"
    , "try"               `fails`     ()
    ]

tryFTests :: [ParserTest ReplCommand]
tryFTests =
    [ "tryf a5"            `parsesTo_` tryFAxiomIndex 5
    , "tryf c5"            `parsesTo_` tryFClaimIndex 5
    , "tryf lbl"           `parsesTo_` tryFRuleName "lbl"
    , "tryf \"my lbl\" "   `parsesTo_` tryFRuleName "my lbl"
    , "tryf albl"          `parsesTo_` tryFRuleName "albl"
    , "tryf clbl"          `parsesTo_` tryFRuleName "clbl"
    , "tryf"               `fails`     ()
    ]

tryAxiomIndex :: Int -> ReplCommand
tryAxiomIndex = Try . ByIndex . Left . AxiomIndex

tryClaimIndex :: Int -> ReplCommand
tryClaimIndex = Try . ByIndex . Right . ClaimIndex

tryRuleName :: String -> ReplCommand
tryRuleName = Try . ByName . RuleName

tryFAxiomIndex :: Int -> ReplCommand
tryFAxiomIndex = TryF . ByIndex . Left . AxiomIndex

tryFClaimIndex :: Int -> ReplCommand
tryFClaimIndex = TryF . ByIndex . Right . ClaimIndex

tryFRuleName :: String -> ReplCommand
tryFRuleName = TryF . ByName . RuleName

exitTests :: [ParserTest ReplCommand]
exitTests =
    [ "exit"  `parsesTo_` Exit
    , "exit " `parsesTo_` Exit
    ]

redirectTests :: [ParserTest ReplCommand]
redirectTests =
    [ "config > file"     `parsesTo_` redirectConfig Nothing "file"
    , "config 5 > file"   `parsesTo_` redirectConfig (Just $ ReplNode 5) "file"
    , "config 5 > file"   `parsesTo_` redirectConfig (Just $ ReplNode 5) "file"
    , "claim 3 > cf"      `parsesTo_` redirectClaim (Just . Left . ClaimIndex $ 3) "cf"
    , "claim 3 > \"c f\"" `parsesTo_` redirectClaim (Just . Left . ClaimIndex $ 3) "c f"
    , "config 5 > "       `fails`     ()
    ]
  where
    redirectConfig maybeNode file  = Redirect (ShowConfig maybeNode) file
    redirectClaim  maybeClaim file = Redirect (ShowClaim maybeClaim) file

pipeTests :: [ParserTest ReplCommand]
pipeTests =
    [ "config | script"                     `parsesTo_` pipeConfig Nothing "script" []
    , "config 5 | script"                   `parsesTo_` pipeConfig (Just (ReplNode 5)) "script" []
    , "config 5 | script \"arg1\" \"arg2\"" `parsesTo_` pipeConfig (Just (ReplNode 5)) "script" ["arg1", "arg2"]
    , "step 5 | script"                     `parsesTo_` pipeStep 5 "script" []
    , "step 5 | \"s c ri p t\""             `parsesTo_` pipeStep 5 "s c ri p t" []
    , "config 5 | "                         `fails`     ()
    ]
  where
    pipeConfig
        :: Maybe ReplNode
        -> String
        -> [String]
        -> ReplCommand
    pipeConfig mrnode s xs =
        Pipe (ShowConfig mrnode) s xs
    pipeStep
        :: Natural
        -> String
        -> [String]
        -> ReplCommand
    pipeStep n s xs =
        Pipe (ProveSteps n) s xs


pipeRedirectTests :: [ParserTest ReplCommand]
pipeRedirectTests =
    [ "config | script > file"
        `parsesTo_` pipeRedirectConfig Nothing "script" [] "file"
    , "config | \"s cript\" \"arg 1\" arg2 > \"f ile\""
        `parsesTo_` pipeRedirectConfig Nothing "s cript" ["arg 1", "arg2"] "f ile"
    , "config 5 | script \"a r g 1\" arg2 > file"
        `parsesTo_` pipeRedirectConfig (Just (ReplNode 5)) "script" ["a r g 1", "arg2"] "file"
    ]

pipeRedirectConfig
    :: Maybe ReplNode
    -> String
    -> [String]
    -> String
    -> ReplCommand
pipeRedirectConfig mrnode s xs file =
    Redirect (Pipe (ShowConfig mrnode) s xs) file

appendTests :: [ParserTest ReplCommand]
appendTests =
    [ "config >> file"        `parsesTo_` AppendTo (ShowConfig Nothing) "file"
    , "config >> \"f i l e\"" `parsesTo_` AppendTo (ShowConfig Nothing) "f i l e"
    , "config >> "            `fails`     ()
    ]

pipeAppendTests :: [ParserTest ReplCommand]
pipeAppendTests =
    [ "config | script >> file"
        `parsesTo_` pipeAppendConfig Nothing "script" [] "file"
    , "config 5 | \"sc ript\" arg1 \"a rg\" >> \"f ile\""
        `parsesTo_` pipeAppendConfig (Just (ReplNode 5)) "sc ript" ["arg1", "a rg"] "f ile"
    ]

pipeAppendConfig
    :: Maybe ReplNode
    -> String
    -> [String]
    -> String
    -> ReplCommand
pipeAppendConfig mrnode s xs file =
    AppendTo (Pipe (ShowConfig mrnode) s xs) file

ruleTests :: [ParserTest ReplCommand]
ruleTests =
    [ "rule"    `parsesTo_` ShowRule Nothing
    , "rule "   `parsesTo_` ShowRule Nothing
    , "rule 5"  `parsesTo_` ShowRule (Just (ReplNode 5))
    , "rule 5 " `parsesTo_` ShowRule (Just (ReplNode 5))
    , "rule -5" `fails`     ()
    ]

clearTests :: [ParserTest ReplCommand]
clearTests =
    [ "clear"    `parsesTo_` Clear Nothing
    , "clear "   `parsesTo_` Clear Nothing
    , "clear 5"  `parsesTo_` Clear (Just (ReplNode 5))
    , "clear 5 " `parsesTo_` Clear (Just (ReplNode 5))
    , "clear -5" `fails`     ()
    ]

saveSessionTests :: [ParserTest ReplCommand]
saveSessionTests =
    [ "save-session file"  `parsesTo_` SaveSession "file"
    , "save-session file " `parsesTo_` SaveSession "file"
    , "save-session"       `fails`     ()
    ]

noArgsAliasTests :: [ParserTest ReplCommand]
noArgsAliasTests =
    [ "alias a = help"              `parsesTo_` alias "help"
    , "alias a = config 10"         `parsesTo_` alias "config 10"
    , "alias a = config 10 | c"     `parsesTo_` alias "config 10 | c"
    , "alias a = config 10 > f"     `parsesTo_` alias "config 10 > f"
    , "alias a = config 10 | c > f" `parsesTo_` alias "config 10 | c > f"
    ]
  where
    alias        = Alias . AliasDefinition "a" []

tryAliasTests :: [ParserTest ReplCommand]
tryAliasTests =
    [ "whatever"    `parsesTo_` tryAlias "whatever" []
    , "c 1 \"a b\"" `parsesTo_` tryAlias "c" [str "1", quoted "a b"]
    ]
  where
    tryAlias name = TryAlias . ReplAlias name
    str = SimpleArgument
    quoted = QuotedArgument

aliasesWithArgs :: [ParserTest ReplCommand]
aliasesWithArgs =
    [ "alias s n = step n"         `parsesTo_` alias "s" ["n"] "step n"
    , "alias s = step 1 > \"a b\"" `parsesTo_` alias "s" [] "step 1 > \"a b\""
    , "alias c n s = config n | echo \"hello world\" > s"
            `parsesTo_` alias "c" ["n", "s"] "config n | echo \"hello world\" > s"
    ]
  where
    alias name arguments command =
        Alias $ AliasDefinition { name, arguments, command }

loadScriptTests :: [ParserTest ReplCommand]
loadScriptTests =
    [ "load file"      `parsesTo_` LoadScript "file"
    , "load file "     `parsesTo_` LoadScript "file"
    , "load \"f ile\"" `parsesTo_` LoadScript "f ile"
    , "load"           `fails`     ()
    ]

initScriptTests :: [ParserTest [ReplCommand]]
initScriptTests =
    [ let
        script1 =
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
      in
        script1 `parsesTo_` commands1
    ]

logTests :: [ParserTest ReplCommand]
logTests =
    [ "log debug [] none"
        `parsesTo_` Log Logger.Debug mempty NoLogging
    , "log critical [scope1] stdout"
        `parsesTo_` Log Logger.Critical (makeLogScope ["scope1"]) LogToStdOut
    , "log info [ scope1,  scope2 ] file \"f s\""
        `parsesTo_` Log Logger.Info (makeLogScope ["scope1", "scope2"]) (LogToFile "f s")
    , "log info [ scope1  scope2 ] file \"f s\""
        `parsesTo_` Log Logger.Info (makeLogScope ["scope1", "scope2"]) (LogToFile "f s")
    ]
