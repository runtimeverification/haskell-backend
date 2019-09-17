module Test.Kore.Strategies.AllPath.Verification
    ( test_allPathVerification
    ) where

import Test.Tasty
    ( TestTree
    )
import Test.Tasty.HUnit
    ( testCase
    )

import Control.Monad.Trans.Except
    ( runExceptT
    )
import Data.Default
    ( def
    )
import Data.Limit
    ( Limit (..)
    )
import Numeric.Natural
    ( Natural
    )

import qualified Kore.Attribute.Axiom as Attribute
import Kore.Internal.Pattern
    ( Conditional (Conditional)
    )
import Kore.Internal.Pattern as Conditional
    ( Conditional (..)
    )
import Kore.Internal.Pattern as Pattern
import Kore.Internal.TermLike
import Kore.Predicate.Predicate
    ( makeEqualsPredicate
    , makeNotPredicate
    , makeTruePredicate
    )
import Kore.Step.Rule
    ( AllPathRule (..)
    , RewriteRule (..)
    , RulePattern (RulePattern)
    )
import Kore.Step.Rule as RulePattern
    ( RulePattern (..)
    )
import Kore.Strategies.Goal
import qualified Kore.Strategies.Verification as AllPath

import Test.Kore.Comparators ()
import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification
import Test.Tasty.HUnit.Extensions

import Debug.Trace
import Kore.Unparser

test_allPathVerification :: [TestTree]
test_allPathVerification =
    [ testCase "Provable using one-path; not provable using all-path" $ do
        -- Axioms:
        --     a => b
        --     a => c
        -- Claim: a => b
        -- Expected: error c
        actual <- runVerification
            (Limit 5)
            [ simpleAxiom Mock.a Mock.b
            , simpleAxiom Mock.a Mock.c
            ]
            [ simpleClaim Mock.a Mock.b ]
        assertEqualWithExplanation ""
            (Left $ Pattern.fromTermLike Mock.c)
            actual
    ]

simpleAxiom
    :: TermLike Variable
    -> TermLike Variable
    -> Rule (AllPathRule Variable)
simpleAxiom left right =
    AllPathRewriteRule $ simpleRewrite left right

simpleClaim
    :: TermLike Variable
    -> TermLike Variable
    -> AllPathRule Variable
simpleClaim left right =
    AllPathRule . getRewriteRule $ simpleRewrite left right

-- TODO: use rulePattern
simpleRewrite
    :: TermLike Variable
    -> TermLike Variable
    -> RewriteRule Variable
simpleRewrite left right =
    RewriteRule RulePattern
        { left = left
        , right = right
        , requires = makeTruePredicate
        , ensures = makeTruePredicate
        , attributes = def
        }

runVerification
    :: AllPath.Claim claim
    => ProofState claim (Pattern Variable) ~ AllPath.CommonProofState
    => Show claim
    => Show (Rule claim)
    => Limit Natural
    -> [Rule claim]
    -> [claim]
    -> IO (Either (Pattern Variable) ())
runVerification stepLimit axioms claims =
    runSimplifier mockEnv
    $ runExceptT
    $ AllPath.verify
        (strategy claims axioms)
        (map applyStepLimit . selectUntrusted $ claims)
  where
    mockEnv = Mock.env
    applyStepLimit claim = (claim, stepLimit)
    selectUntrusted = filter (not . isTrusted)
