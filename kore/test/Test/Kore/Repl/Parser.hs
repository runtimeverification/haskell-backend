module Test.Kore.Repl.Parser
    ( test_replParser
    ) where

import Test.Tasty
       ( TestTree, testGroup )

import Kore.Repl.Data
import Kore.Repl.Parser

import Test.Kore.Parser

test_replParser :: [TestTree]
test_replParser =
    [ helpTests        `tests` "help"
    , claimTests       `tests` "claim"
    , axiomTests       `tests` "axiom"
    , proveTests       `tests` "prove"
    , graphTests       `tests` "graph"
    , stepTests        `tests` "step"
    , selectTests      `tests` "select"
    , configTests      `tests` "config"
    , leafsTests       `tests` "leafs"
    , precBranchTests  `tests` "prec-branch"
    , childrenTests    `tests` "children"
    , exitTests        `tests` "exit"
    , omitTests        `tests` "omit"
    , labelTests       `tests` "label"
    , redirectTests    `tests` "redirect"
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
    [ "claim 0"  `parsesTo_` ShowClaim 0
    , "claim 0 " `parsesTo_` ShowClaim 0
    , "claim 5"  `parsesTo_` ShowClaim 5
    , "claim"    `fails`     "needs parameters"
    , "claim -5" `fails`     "no negative numbers"
    ]

axiomTests :: [ParserTest ReplCommand]
axiomTests =
    [ "axiom 0"  `parsesTo_` ShowAxiom 0
    , "axiom 0 " `parsesTo_` ShowAxiom 0
    , "axiom 5"  `parsesTo_` ShowAxiom 5
    , "axiom"    `fails`     "needs parameters"
    , "axiom -5" `fails`     "no negative numbers"
    ]

proveTests :: [ParserTest ReplCommand]
proveTests =
    [ "prove 0"  `parsesTo_` Prove 0
    , "prove 0 " `parsesTo_` Prove 0
    , "prove 5"  `parsesTo_` Prove 5
    , "prove"    `fails`     "needs parameters"
    , "prove -5" `fails`     "no negative numbers"
    ]

graphTests :: [ParserTest ReplCommand]
graphTests =
    [ "graph"  `parsesTo_` ShowGraph
    , "graph " `parsesTo_` ShowGraph
    ]

stepTests :: [ParserTest ReplCommand]
stepTests =
    [ "step"    `parsesTo_` ProveSteps 1
    , "step "   `parsesTo_` ProveSteps 1
    , "step 5"  `parsesTo_` ProveSteps 5
    , "step 5 " `parsesTo_` ProveSteps 5
    , "step -5" `fails`     "no negative numbers"
    ]

selectTests :: [ParserTest ReplCommand]
selectTests =
    [ "select 5"  `parsesTo_` SelectNode 5
    , "select 5 " `parsesTo_` SelectNode 5
    , "select -5" `fails`     "no negative numbers"
    ]

configTests :: [ParserTest ReplCommand]
configTests =
    [ "config"    `parsesTo_` ShowConfig Nothing
    , "config "   `parsesTo_` ShowConfig Nothing
    , "config 5"  `parsesTo_` ShowConfig (Just 5)
    , "config -5" `fails`     "no negative numbers"
    ]

omitTests :: [ParserTest ReplCommand]
omitTests =
    [ "omit"        `parsesTo_` OmitCell Nothing
    , "omit "       `parsesTo_` OmitCell Nothing
    , "omit   "     `parsesTo_` OmitCell Nothing
    , "omit k"      `parsesTo_` OmitCell (Just "k")
    , "omit k "     `parsesTo_` OmitCell (Just "k")
    , "omit state " `parsesTo_` OmitCell (Just "state")
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
    , "prec-branch 5"  `parsesTo_` ShowPrecBranch (Just 5)
    , "prec-branch -5" `fails`     "no negative numbers"
    ]

childrenTests :: [ParserTest ReplCommand]
childrenTests =
    [ "children"    `parsesTo_` ShowChildren Nothing
    , "children "   `parsesTo_` ShowChildren Nothing
    , "children 5"  `parsesTo_` ShowChildren (Just 5)
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
    , "label +label 5"  `parsesTo_` LabelAdd "label" (Just 5)
    , "label +1ab31 5"  `parsesTo_` LabelAdd "1ab31" (Just 5)
    , "label -label"    `parsesTo_` LabelDel "label"
    , "label -1ab31"    `parsesTo_` LabelDel "1ab31"
    , "label +-"        `fails`     "can't both add and remove"
    , "label +label -5" `fails`     "no negative numbers"
    ]

exitTests :: [ParserTest ReplCommand]
exitTests =
    [ "exit"  `parsesTo_` Exit
    , "exit " `parsesTo_` Exit
    ]

redirectTests :: [ParserTest ReplCommand]
redirectTests =
    [ "config > file"   `parsesTo_` Redirect (ShowConfig Nothing)  "file"
    , "config 5 > file" `parsesTo_` Redirect (ShowConfig (Just 5)) "file"
    , "config 5 > file" `parsesTo_` Redirect (ShowConfig (Just 5)) "file"
    , "claim 3 > cf"    `parsesTo_` Redirect (ShowClaim 3)         "cf"
    ]
