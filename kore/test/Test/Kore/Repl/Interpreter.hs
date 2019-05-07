module Test.Kore.Repl.Interpreter
    ( test_replInterpreter
    ) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( testCase, (@?=) )

import           Control.Monad.Trans.State.Strict
                 ( runStateT )
import           Data.Coerce
                 ( coerce )
import qualified Data.Map as Map
import qualified Data.Sequence as Seq

import           Kore.Internal.TermLike
                 ( mkBottom_ )
import           Kore.Repl.Data
import           Kore.Repl.Interpreter
import           Kore.Step.Rule
                 ( OnePathRule (..), rulePattern )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Syntax.Variable
                 ( Variable )
import qualified SMT

import Test.Kore
import Test.Kore.Parser

type Claim = OnePathRule Variable

test_replInterpreter :: [TestTree]
test_replInterpreter =
    [ showUsageTests `tests` "ShowUsage"
    , helpTests      `tests` "Help"
    ]

showUsageTests :: [Assertion]
showUsageTests =
    [ ShowUsage `interpretsTo_` Result
                                    { output   = showUsageMessage <> "\n"
                                    , continue = True
                                    , state    = id
                                    }
    ]
helpTests :: [Assertion]
helpTests =
    [ Help      `interpretsTo_` Result
                                    { output   = helpText <> "\n"
                                    , continue = True
                                    , state    = id
                                    }
    ]

data Result = Result
    { output   :: String
    , continue :: Bool
    , state    :: ReplState Claim -> ReplState Claim
    }

data Assertion = Assertion
    { command :: ReplCommand
    , result  :: Result
    }

tests :: [Assertion] -> String -> TestTree
tests ts pname =
    testGroup
        ("REPL.Interpreter." <> pname)
        $ assertionToTest <$> ts

emptyState :: ReplState Claim
emptyState =
    ReplState
        { axioms   = []
        , claims   = []
        , claim    = claim'
        , graph    = graph'
        , node     = ReplNode 0
        , commands = Seq.empty
        , omit    = []
        , stepper = stepper0
        , unifier = unifier0
        , labels  = Map.empty
        }
  where
    claim' = coerce $ rulePattern mkBottom_ mkBottom_
    graph' = emptyExecutionGraph claim'
    stepper0 _ _ _ _ _ = return graph'
unifier0 _ _ = return ()

assertionToTest :: Assertion -> TestTree
assertionToTest Assertion { command, result } = testCase "" $ do
    (c, s) <- liftSimplifier $
        replInterpreter validateOutput command `runStateT` emptyState
    c @?= continue result
    s @?= (state result) emptyState
  where
    liftSimplifier = SMT.runSMT SMT.defaultConfig . evalSimplifier emptyLogger
    validateOutput out = out @?= output result

interpretsTo_ :: ReplCommand -> Result -> Assertion
interpretsTo_ = Assertion
