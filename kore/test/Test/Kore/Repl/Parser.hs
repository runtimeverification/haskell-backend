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
    , showLabelsTests  `tests` "labels"
    , setLabelTests    `tests` "set-label"
    , gotoLabelTests   `tests` "goto-label"
    , removeLabelTests `tests` "remove-label"
    , omitTests        `tests` "omit"
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
    , "claim"    `failsWith` "<test-string>:1:6:\n\
                             \  |\n\
                             \1 | claim\n\
                             \  |      ^\n\
                             \unexpected end of input\n\
                             \expecting integer or white space\n"
    , "claim -5" `failsWith` "<test-string>:1:7:\n\
                             \  |\n\
                             \1 | claim -5\n\
                             \  |       ^\n\
                             \unexpected '-'\n\
                             \expecting integer or white space\n"
    ]

axiomTests :: [ParserTest ReplCommand]
axiomTests =
    [ "axiom 0"  `parsesTo`   ShowAxiom 0
    , "axiom 0 " `parsesTo`   ShowAxiom 0
    , "axiom 5"  `parsesTo`   ShowAxiom 5
    , "axiom"    `failsWith`  "<test-string>:1:6:\n\
                              \  |\n\
                              \1 | axiom\n\
                              \  |      ^\n\
                              \unexpected end of input\n\
                              \expecting integer or white space\n"
    , "axiom -5"  `failsWith` "<test-string>:1:7:\n\
                              \  |\n\
                              \1 | axiom -5\n\
                              \  |       ^\n\
                              \unexpected '-'\n\
                              \expecting integer or white space\n"
    ]

proveTests :: [ParserTest ReplCommand]
proveTests =
    [ "prove 0"  `parsesTo`   Prove 0
    , "prove 0 " `parsesTo`   Prove 0
    , "prove 5"  `parsesTo`   Prove 5
    , "prove"    `failsWith`  "<test-string>:1:6:\n\
                              \  |\n\
                              \1 | prove\n\
                              \  |      ^\n\
                              \unexpected end of input\n\
                              \expecting integer or white space\n"
    , "prove -5"  `failsWith` "<test-string>:1:7:\n\
                              \  |\n\
                              \1 | prove -5\n\
                              \  |       ^\n\
                              \unexpected '-'\n\
                              \expecting integer or white space\n"
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
    , "step -5" `failsWith` "<test-string>:1:6:\n\
                            \  |\n\
                            \1 | step -5\n\
                            \  |      ^\n\
                            \unexpected '-'\n\
                            \expecting end of input, integer, or white space\n"
    ]

selectTests :: [ParserTest ReplCommand]
selectTests =
    [ "select 5"  `parsesTo`  SelectNode 5
    , "select 5 " `parsesTo`  SelectNode 5
    , "select -5" `failsWith` "<test-string>:1:8:\n\
                              \  |\n\
                              \1 | select -5\n\
                              \  |        ^\n\
                              \unexpected '-'\n\
                              \expecting integer or white space\n"
    ]

configTests :: [ParserTest ReplCommand]
configTests =
    [ "config"    `parsesTo`  ShowConfig Nothing
    , "config "   `parsesTo`  ShowConfig Nothing
    , "config 5"  `parsesTo`  ShowConfig (Just 5)
    , "config -5" `failsWith` "<test-string>:1:8:\n\
                              \  |\n\
                              \1 | config -5\n\
                              \  |        ^\n\
                              \unexpected '-'\n\
                              \expecting end of input, integer, or white space\n"
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
    , "prec-branch -5" `failsWith` "<test-string>:1:13:\n\
                                    \  |\n\
                                    \1 | prec-branch -5\n\
                                    \  |             ^\n\
                                    \unexpected '-'\n\
                                    \expecting end of input, integer, or white space\n"
    ]

childrenTests :: [ParserTest ReplCommand]
childrenTests =
    [ "children"    `parsesTo`  ShowChildren Nothing
    , "children "   `parsesTo`  ShowChildren Nothing
    , "children 5"  `parsesTo`  ShowChildren (Just 5)
    , "children -5" `failsWith` "<test-string>:1:10:\n\
                                 \  |\n\
                                 \1 | children -5\n\
                                 \  |          ^\n\
                                 \unexpected '-'\n\
                                 \expecting end of input, integer, or white space\n"
    ]

showLabelsTests :: [ParserTest ReplCommand]
showLabelsTests =
    [ "labels"  `parsesTo` ShowLabels
    , "labels " `parsesTo` ShowLabels
    ]

setLabelTests :: [ParserTest ReplCommand]
setLabelTests =
    [ "set-label l 5"      `parsesTo` SetLabel "l" 5
    , "set-label label 5"  `parsesTo` SetLabel "label" 5
    , "set-label 1ab31 5"  `parsesTo` SetLabel "1ab31" 5
    , "set-label 1ab31 5 " `parsesTo` SetLabel "1ab31" 5
    , "set-label 5"        `failsWith` "<test-string>:1:12:\n\
                                        \  |\n\
                                        \1 | set-label 5\n\
                                        \  |            ^\n\
                                        \unexpected end of input\n\
                                        \expecting alphanumeric character, integer, or white space\n"
    , "set-label 5 "       `failsWith` "<test-string>:1:13:\n\
                                        \  |\n\
                                        \1 | set-label 5 \n\
                                        \  |             ^\n\
                                        \unexpected end of input\n\
                                        \expecting integer or white space\n"
    , "set-label label -5" `failsWith` "<test-string>:1:17:\n\
                                        \  |\n\
                                        \1 | set-label label -5\n\
                                        \  |                 ^\n\
                                        \unexpected '-'\n\
                                        \expecting integer or white space\n"
    ]

gotoLabelTests :: [ParserTest ReplCommand]
gotoLabelTests =
    [ "goto-label l"      `parsesTo` GotoLabel "l"
    , "goto-label label"  `parsesTo` GotoLabel "label"
    , "goto-label 1ab31"  `parsesTo` GotoLabel "1ab31"
    , "goto-label 1ab31 " `parsesTo` GotoLabel "1ab31"
    , "goto-label"        `failsWith` "<test-string>:1:11:\n\
                                       \  |\n\
                                       \1 | goto-label\n\
                                       \  |           ^\n\
                                       \unexpected end of input\n\
                                       \expecting alphanumeric character or white space\n"
    , "goto-label "       `failsWith` "<test-string>:1:12:\n\
                                       \  |\n\
                                       \1 | goto-label \n\
                                       \  |            ^\n\
                                       \unexpected end of input\n\
                                       \expecting alphanumeric character or white space\n"
    ]

removeLabelTests :: [ParserTest ReplCommand]
removeLabelTests =
    [ "remove-label l"      `parsesTo` RemoveLabel "l"
    , "remove-label label"  `parsesTo` RemoveLabel "label"
    , "remove-label 1ab31"  `parsesTo` RemoveLabel "1ab31"
    , "remove-label 1ab31 " `parsesTo` RemoveLabel "1ab31"
    , "remove-label"        `failsWith` "<test-string>:1:13:\n\
                                         \  |\n\
                                         \1 | remove-label\n\
                                         \  |             ^\n\
                                         \unexpected end of input\n\
                                         \expecting alphanumeric character or white space\n"
    , "remove-label "       `failsWith` "<test-string>:1:14:\n\
                                         \  |\n\
                                         \1 | remove-label \n\
                                         \  |              ^\n\
                                         \unexpected end of input\n\
                                         \expecting alphanumeric character or white space\n"
    ]
exitTests :: [ParserTest ReplCommand]
exitTests =
    [ "exit"  `parsesTo` Exit
    , "exit " `parsesTo` Exit
    ]
