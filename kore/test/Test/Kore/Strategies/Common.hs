module Test.Kore.Strategies.Common
    ( simpleRewrite
    , runVerification
    ) where

import Control.Monad.Trans.Except
    ( runExceptT
    )
import Data.Limit
    ( Limit (..)
    )
import Numeric.Natural
    ( Natural
    )

import Kore.Internal.Pattern
    ( Pattern
    )
import Kore.Internal.TermLike
import Kore.Step.RulePattern
    ( RewriteRule (..)
    , rulePattern
    )
import Kore.Step.Strategy
    ( GraphSearchOrder (..)
    )
import Kore.Strategies.Goal
import qualified Kore.Strategies.Verification as Verification

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification

simpleRewrite
    :: TermLike Variable
    -> TermLike Variable
    -> RewriteRule Variable
simpleRewrite left right =
    RewriteRule $ rulePattern left right

runVerification
    :: Verification.Claim claim
    => ProofState claim (Pattern Variable) ~ Verification.CommonProofState
    => Show claim
    => Show (Rule claim)
    => Limit Natural
    -> Limit Natural
    -> [Rule claim]
    -> [claim]
    -> IO (Either (Pattern Variable) ())
runVerification breadthLimit depthLimit axioms claims =
    runSimplifier mockEnv
    $ runExceptT
    $ Verification.verify
        breadthLimit
        BreadthFirst
        claims
        axioms
        (map applyDepthLimit . selectUntrusted $ claims)
  where
    mockEnv = Mock.env
    applyDepthLimit claim = (claim, depthLimit)
    selectUntrusted = filter (not . isTrusted)
