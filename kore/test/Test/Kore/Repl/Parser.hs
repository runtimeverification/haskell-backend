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
    [ helpTests       `tests` "help"
    , claimTests      `tests` "claim"
    , axiomTests      `tests` "axiom"
    , proveTests      `tests` "prove"
    , graphTests      `tests` "graph"
    , stepTests       `tests` "step"
    , selectTests     `tests` "select"
    , configTests     `tests` "config"
    , omitTests       `tests` "omit"
    , leafsTests      `tests` "leafs"
    , precBranchTests `tests` "prec-branch"
    , childrenTests   `tests` "children"
    , exitTests       `tests` "exit"
    , redirectTests   `tests` "redirect"
    ]

tests :: [ParserTest ReplCommand] -> String -> TestTree
tests ts pname =
    testGroup
        ("REPL.Parser." <> pname)
        . parseTree commandParser
        $ ts

helpTests :: [ParserTest ReplCommand]
helpTests =
    [ "help"  `parsesTo` Help
    , "help " `parsesTo` Help
    ]

claimTests :: [ParserTest ReplCommand]
claimTests =
    [ "claim 0"  `parsesTo`  ShowClaim 0
    , "claim 0 " `parsesTo`  ShowClaim 0
    , "claim 5"  `parsesTo`  ShowClaim 5
    , "claim"    `failsWith` "needs parameters"
    , "claim -5" `failsWith` "no negative numbers"
    ]

axiomTests :: [ParserTest ReplCommand]
axiomTests =
    [ "axiom 0"  `parsesTo`   ShowAxiom 0
    , "axiom 0 " `parsesTo`   ShowAxiom 0
    , "axiom 5"  `parsesTo`   ShowAxiom 5
    , "axiom"    `failsWith`  "needs parameters"
    , "axiom -5"  `failsWith` "no negative numbers"
    ]

proveTests :: [ParserTest ReplCommand]
proveTests =
    [ "prove 0"  `parsesTo`   Prove 0
    , "prove 0 " `parsesTo`   Prove 0
    , "prove 5"  `parsesTo`   Prove 5
    , "prove"    `failsWith`  "needs parameters"
    , "prove -5"  `failsWith` "no negative numbers"
    ]

graphTests :: [ParserTest ReplCommand]
graphTests =
    [ "graph"  `parsesTo` ShowGraph
    , "graph " `parsesTo` ShowGraph
    ]

stepTests :: [ParserTest ReplCommand]
stepTests =
    [ "step"    `parsesTo`  ProveSteps 1
    , "step "   `parsesTo`  ProveSteps 1
    , "step 5"  `parsesTo`  ProveSteps 5
    , "step 5 " `parsesTo`  ProveSteps 5
    , "step -5" `failsWith` "no negative numbers"
    ]

selectTests :: [ParserTest ReplCommand]
selectTests =
    [ "select 5"  `parsesTo`  SelectNode 5
    , "select 5 " `parsesTo`  SelectNode 5
    , "select -5" `failsWith` "no negative numbers"
    ]

configTests :: [ParserTest ReplCommand]
configTests =
    [ "config"    `parsesTo`  ShowConfig Nothing
    , "config "   `parsesTo`  ShowConfig Nothing
    , "config 5"  `parsesTo`  ShowConfig (Just 5)
    , "config -5" `failsWith` "no negative numbers"
    ]

omitTests :: [ParserTest ReplCommand]
omitTests =
    [ "omit"        `parsesTo` OmitCell Nothing
    , "omit "       `parsesTo` OmitCell Nothing
    , "omit   "     `parsesTo` OmitCell Nothing
    , "omit k"      `parsesTo` OmitCell (Just "k")
    , "omit k "     `parsesTo` OmitCell (Just "k")
    , "omit state " `parsesTo` OmitCell (Just "state")
    ]

leafsTests :: [ParserTest ReplCommand]
leafsTests =
    [ "leafs"  `parsesTo` ShowLeafs
    , "leafs " `parsesTo` ShowLeafs
    ]

precBranchTests :: [ParserTest ReplCommand]
precBranchTests =
    [ "prec-branch"    `parsesTo`  ShowPrecBranch Nothing
    , "prec-branch "   `parsesTo`  ShowPrecBranch Nothing
    , "prec-branch 5"  `parsesTo`  ShowPrecBranch (Just 5)
    , "prec-branch -5" `failsWith` "no negative numbers"
    ]

childrenTests :: [ParserTest ReplCommand]
childrenTests =
    [ "children"    `parsesTo`  ShowChildren Nothing
    , "children "   `parsesTo`  ShowChildren Nothing
    , "children 5"  `parsesTo`  ShowChildren (Just 5)
    , "children -5" `failsWith` "no negative numbers"
    ]

exitTests :: [ParserTest ReplCommand]
exitTests =
    [ "exit"  `parsesTo` Exit
    , "exit " `parsesTo` Exit
    ]

redirectTests :: [ParserTest ReplCommand]
redirectTests =
    [ "config > file"    `parsesTo` Redirect (ShowConfig Nothing)  "file"
    , "config 5 > file"  `parsesTo` Redirect (ShowConfig (Just 5)) "file"
    , "config 5 > file"  `parsesTo` Redirect (ShowConfig (Just 5)) "file"
    , "claim 3 > cf"     `parsesTo` Redirect (ShowClaim 3)         "cf"
    ]
