module Test.Kore.Repl.Parser
    ( test_replParser
    ) where

import Numeric.Natural
import Test.Tasty
       ( TestTree, testGroup )

import Kore.Repl.Data
import Kore.Repl.Parser

import Test.Kore.Parser

test_replParser :: [TestTree]
test_replParser =
    [ helpTests         `tests` "help"
    , claimTests        `tests` "claim"
    , axiomTests        `tests` "axiom"
    , proveTests        `tests` "prove"
    , graphTests        `tests` "graph"
    , stepTests         `tests` "step"
    , selectTests       `tests` "select"
    , configTests       `tests` "config"
    , leafsTests        `tests` "leafs"
    , precBranchTests   `tests` "prec-branch"
    , childrenTests     `tests` "children"
    , exitTests         `tests` "exit"
    , omitTests         `tests` "omit"
    , labelTests        `tests` "label"
    , tryTests          `tests` "try"
    , redirectTests     `tests` "redirect"
    , ruleTests         `tests` "rule"
    , stepfTests        `tests` "stepf"
    , clearTests        `tests` "clear"
    , pipeTests         `tests` "pipe"
    , pipeRedirectTests `tests` "pipe redirect"
    , saveSessionTests  `tests` "save-session"
    , appendTests       `tests` "append"
    , pipeAppendTests   `tests` "pipe append"
    , noArgsAliasTests  `tests` "no arguments alias tests"
    ]

tests :: [ParserTest ReplCommand] -> String -> TestTree
tests ts pname =
    testGroup
        ("REPL.Parser." <> pname)
        . parseTree commandParser
        $ ts

helpTests :: [ParserTest ReplCommand]
helpTests =
    [ "help"  `parsesTo_` Help
    , "help " `parsesTo_` Help
    ]

claimTests :: [ParserTest ReplCommand]
claimTests =
    [ "claim 0"  `parsesTo_` ShowClaim (ClaimIndex 0)
    , "claim 0 " `parsesTo_` ShowClaim (ClaimIndex 0)
    , "claim 5"  `parsesTo_` ShowClaim (ClaimIndex 5)
    , "claim"    `fails`     "needs parameters"
    , "claim -5" `fails`     "no negative numbers"
    ]

axiomTests :: [ParserTest ReplCommand]
axiomTests =
    [ "axiom 0"  `parsesTo_` ShowAxiom (AxiomIndex 0)
    , "axiom 0 " `parsesTo_` ShowAxiom (AxiomIndex 0)
    , "axiom 5"  `parsesTo_` ShowAxiom (AxiomIndex 5)
    , "axiom"    `fails`     "needs parameters"
    , "axiom -5" `fails`     "no negative numbers"
    ]

proveTests :: [ParserTest ReplCommand]
proveTests =
    [ "prove 0"  `parsesTo_` Prove (ClaimIndex 0)
    , "prove 0 " `parsesTo_` Prove (ClaimIndex 0)
    , "prove 5"  `parsesTo_` Prove (ClaimIndex 5)
    , "prove"    `fails`     "needs parameters"
    , "prove -5" `fails`     "no negative numbers"
    ]

graphTests :: [ParserTest ReplCommand]
graphTests =
    [ "graph"           `parsesTo_` ShowGraph Nothing
    , "graph "          `parsesTo_` ShowGraph Nothing
    , "graph file"      `parsesTo_` ShowGraph (Just "file")
    , "graph \"f ile\"" `parsesTo_` ShowGraph (Just "f ile")
    , "graph f ile"     `fails`     "graph doesn't take 2 args"
    ]

stepTests :: [ParserTest ReplCommand]
stepTests =
    [ "step"    `parsesTo_` ProveSteps 1
    , "step "   `parsesTo_` ProveSteps 1
    , "step 5"  `parsesTo_` ProveSteps 5
    , "step 5 " `parsesTo_` ProveSteps 5
    , "step -5" `fails`     "no negative numbers"
    ]

stepfTests :: [ParserTest ReplCommand]
stepfTests =
    [ "stepf"    `parsesTo_` ProveStepsF 1
    , "stepf "   `parsesTo_` ProveStepsF 1
    , "stepf 5"  `parsesTo_` ProveStepsF 5
    , "stepf 5 " `parsesTo_` ProveStepsF 5
    , "stepf -5" `fails`     "no negative numbers"
    ]

selectTests :: [ParserTest ReplCommand]
selectTests =
    [ "select 5"  `parsesTo_` SelectNode (ReplNode 5)
    , "select 5 " `parsesTo_` SelectNode (ReplNode 5)
    , "select -5" `fails`     "no negative numbers"
    ]

configTests :: [ParserTest ReplCommand]
configTests =
    [ "config"    `parsesTo_` ShowConfig Nothing
    , "config "   `parsesTo_` ShowConfig Nothing
    , "config 5"  `parsesTo_` ShowConfig (Just (ReplNode 5))
    , "config -5" `fails`     "no negative numbers"
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
    , "prec-branch -5" `fails`     "no negative numbers"
    ]

childrenTests :: [ParserTest ReplCommand]
childrenTests =
    [ "children"    `parsesTo_` ShowChildren Nothing
    , "children "   `parsesTo_` ShowChildren Nothing
    , "children 5"  `parsesTo_` ShowChildren (Just (ReplNode 5))
    , "children -5" `fails`     "no negative numbers"
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
    , "label +label -5" `fails`     "no negative numbers"
    ]

tryTests :: [ParserTest ReplCommand]
tryTests =
    [ "try a5"  `parsesTo_` tryAxiom 5
    , "try c5"  `parsesTo_` tryClaim 5
    , "try"     `fails`     "empty try"
    , "try 5"   `fails`     "need to specify axiom or claim"
    , "try a 5" `fails`     "can't separate specifier and id"
    , "try a"   `fails`     "must specify identifier"
    ]
  where
    tryAxiom :: Int -> ReplCommand
    tryAxiom = Try . Left . AxiomIndex

    tryClaim :: Int -> ReplCommand
    tryClaim = Try . Right . ClaimIndex

exitTests :: [ParserTest ReplCommand]
exitTests =
    [ "exit"  `parsesTo_` Exit
    , "exit " `parsesTo_` Exit
    ]

redirectTests :: [ParserTest ReplCommand]
redirectTests =
    [ "config > file"     `parsesTo_` Redirect (ShowConfig Nothing)  "file"
    , "config 5 > file"   `parsesTo_` Redirect (ShowConfig (Just (ReplNode 5))) "file"
    , "config 5 > file"   `parsesTo_` Redirect (ShowConfig (Just (ReplNode 5))) "file"
    , "claim 3 > cf"      `parsesTo_` Redirect (ShowClaim (ClaimIndex 3)) "cf"
    , "claim 3 > \"c f\"" `parsesTo_` Redirect (ShowClaim (ClaimIndex 3)) "c f"
    , "config 5 > "       `fails`     "no file name"
    ]

pipeTests :: [ParserTest ReplCommand]
pipeTests =
    [ "config | script"                     `parsesTo_` pipeConfig Nothing "script" []
    , "config 5 | script"                   `parsesTo_` pipeConfig (Just (ReplNode 5)) "script" []
    , "config 5 | script \"arg1\" \"arg2\"" `parsesTo_` pipeConfig (Just (ReplNode 5)) "script" ["arg1", "arg2"]
    , "step 5 | script"                     `parsesTo_` pipeStep 5 "script" []
    , "step 5 | \"s c ri p t\""             `parsesTo_` pipeStep 5 "s c ri p t" []
    , "config 5 | "                         `fails`     "no script name"
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
    , "config 5 | > "        `fails`     "no script or file name"
    , "config 5 | script > " `fails`     "no file name"
    , "config 5 | > file"    `fails`     "no script name"
    ]
  where
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
    , "config >> "            `fails`     "no file name"
    ]

pipeAppendTests :: [ParserTest ReplCommand]
pipeAppendTests =
    [ "config | script >> file"
        `parsesTo_` pipeAppendConfig Nothing "script" [] "file"
    , "config 5 | \"sc ript\" arg1 \"a rg\" >> \"f ile\""
        `parsesTo_` pipeAppendConfig (Just (ReplNode 5)) "sc ript" ["arg1", "a rg"] "f ile"
    , "config | > >> file" `fails` "incorrect script name"
    , "config | s >> "     `fails` "no file name"
    ]
  where
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
    , "rule -5" `fails`     "no negative numbers"
    ]

clearTests :: [ParserTest ReplCommand]
clearTests =
    [ "clear"    `parsesTo_` Clear Nothing
    , "clear "   `parsesTo_` Clear Nothing
    , "clear 5"  `parsesTo_` Clear (Just (ReplNode 5))
    , "clear 5 " `parsesTo_` Clear (Just (ReplNode 5))
    , "clear -5" `fails`     "no negative numbers"
    ]

saveSessionTests :: [ParserTest ReplCommand]
saveSessionTests =
    [ "save-session file"  `parsesTo_` SaveSession "file"
    , "save-session file " `parsesTo_` SaveSession "file"
    , "save-session"       `fails`     "need to supply file name"
    ]

noArgsAliasTests :: [ParserTest ReplCommand]
noArgsAliasTests =
    [ "alias a = help"                   `parsesTo_` alias Help
    , "alias a = config 10"              `parsesTo_` alias config10
    , "alias a = config 10 | cmd"        `parsesTo_` alias pipeCmd
    , "alias a = config 10 > file"       `parsesTo_` alias redirectFile
    , "alias a = config 10 | cmd > file" `parsesTo_` alias pipeRedirect
    ]
  where
    alias = Alias . ReplAlias "a"
    config10 = ShowConfig . Just . ReplNode $ 10
    pipeCmd      = Pipe config10 "cmd" []
    redirectFile = Redirect config10 "file"
    pipeRedirect = Redirect pipeCmd "file"
