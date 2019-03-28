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
    [ helpTests   `tests` "help"
    , claimTests  `tests` "claim"
    , axiomTests  `tests` "axiom"
    , proveTests  `tests` "prove"
    , graphTests  `tests` "graph"
    , stepTests   `tests` "step"
    , selectTests `tests` "select"
    , configTests `tests` "config"
    , leafsTests  `tests` "leafs"
    , exitTests   `tests` "exit"
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

leafsTests :: [ParserTest ReplCommand]
leafsTests =
    [ "leafs"  `parsesTo` ShowLeafs
    , "leafs " `parsesTo` ShowLeafs
    ]

exitTests :: [ParserTest ReplCommand]
exitTests =
    [ "exit"  `parsesTo` Exit
    , "exit " `parsesTo` Exit
    ]
