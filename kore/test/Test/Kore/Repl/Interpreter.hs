module Test.Kore.Repl.Interpreter
    ( test_replInterpreter
    ) where

import Test.Tasty
       ( TestTree, testGroup )
import Test.Tasty.HUnit
       ( assertBool, testCase, (@?=) )

import           Control.Monad.Trans.State.Strict
                 ( runStateT )
import           Data.Coerce
                 ( coerce )
import           Data.IORef
                 ( newIORef, readIORef, writeIORef )
import qualified Data.Map as Map
import qualified Data.Sequence as Seq

import qualified Kore.Builtin.Int as Int
import           Kore.Domain.Builtin
                 ( InternalInt (..) )
import           Kore.Internal.TermLike
                 ( mkApp, mkBottom_, mkVar, varS )
import           Kore.OnePath.Verification
                 ( Axiom (..), verifyClaimStep )
import           Kore.Repl.Data
import           Kore.Repl.Interpreter
import           Kore.Step.Rule
                 ( OnePathRule (..), RewriteRule (..), rulePattern )
import           Kore.Step.Simplification.Data
                 ( evalSimplifier )
import           Kore.Syntax.Variable
                 ( Variable )
import qualified SMT

import Test.Kore
import Test.Kore.Builtin.Builtin
import Test.Kore.Builtin.Definition
import Test.Kore.Parser

type Claim = OnePathRule Variable

test_replInterpreter :: [TestTree]
test_replInterpreter =
    [ showUsageTests `tests` "ShowUsage"
    , helpTests      `tests` "Help"
    , sampleTest
    ]

showUsageTests :: [Assertion]
showUsageTests =
    [ ShowUsage `interpretsTo_` Result
                                    { output   = showUsageMessage <> "\n"
                                    , continue = True
                                    , state    = const True
                                    }
    ]

helpTests :: [Assertion]
helpTests =
    [ Help      `interpretsTo_` Result
                                    { output   = helpText <> "\n"
                                    , continue = True
                                    , state    = const True
                                    }
    ]

sampleTest :: TestTree
sampleTest =
    let
        axioms = [ add1 ]
        claim  = zeroToTen
        command = ProveSteps 5
    in testCase "asdf" $ do
        Result' { output', continue', state' } <- run command axioms claim
        output'     @?= ""
        continue'   @?= True
        node state' @?= ReplNode 5

add1 :: Axiom
add1 = coerce $ rulePattern n plusOne
  where
    one     = Int.asTermLike $ InternalInt intSort 1
    n       = mkVar $ varS "x" intSort
    plusOne = mkApp intSort addIntSymbol [n, one]

zeroToTen :: Claim
zeroToTen = coerce $ rulePattern zero ten
  where
    zero = Int.asTermLike $ InternalInt intSort 0
    ten  = Int.asTermLike $ InternalInt intSort 10

run :: ReplCommand -> [Axiom] -> Claim -> IO Result'
run command axioms claim =  do
    output <- newIORef ""
    (c, s) <- liftSimplifier $
        replInterpreter (writeIORef output) command `runStateT` state
    output' <- readIORef output
    return $ Result' output' c s
  where
    liftSimplifier = SMT.runSMT SMT.defaultConfig . evalSimplifier emptyLogger
    state = mkState axioms claim

data Result' = Result'
    { output'   :: String
    , continue' :: Bool
    , state'    :: ReplState Claim
    }

data Result = Result
    { output   :: String
    , continue :: Bool
    , state    :: ReplState Claim -> Bool
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

mkState :: [Axiom] -> Claim -> ReplState Claim
mkState axioms claim =
    ReplState
        { axioms   = axioms
        , claims   = [claim]
        , claim    = claim
        , graph    = graph'
        , node     = ReplNode 0
        , commands = Seq.empty
        , omit    = []
        , stepper = stepper0
        , unifier = unifier0
        , labels  = Map.empty
        }
  where
    graph' = emptyExecutionGraph claim
    stepper0 claim claims axioms graph (ReplNode node) =
        verifyClaimStep
            testMetadataTools
            doNothingSimplifier
            testSubstitutionSimplifier
            evaluators
            claim
            claims
            axioms
            graph
            node
    unifier0 _ _ = return ()

assertionToTest :: Assertion -> TestTree
assertionToTest Assertion { command, result } = testCase "" $ do
    (c, s) <- liftSimplifier $
        replInterpreter validateOutput command `runStateT` emptyState
    c @?= continue result
    assertBool "" $ (state result) s
  where
    liftSimplifier = SMT.runSMT SMT.defaultConfig . evalSimplifier emptyLogger
    validateOutput out = out @?= output result

interpretsTo_ :: ReplCommand -> Result -> Assertion
interpretsTo_ = Assertion
