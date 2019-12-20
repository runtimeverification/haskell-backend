module Test.Kore.Strategies.Common
    ( simpleRewrite
    , runVerification
    , runVerificationToPattern
    ) where

import Control.DeepSeq
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
import Kore.Step.Rule
    ( RewriteRule (..)
    , rulePattern
    )
import Kore.Step.Strategy
    ( GraphSearchOrder (..)
    )
import Kore.Strategies.Goal
import Kore.Strategies.Verification
    ( StuckVerification (StuckVerification)
    )
import qualified Kore.Strategies.Verification as Verification

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification

simpleRewrite
    :: TermLike Variable
    -> TermLike Variable
    -> RewriteRule Variable
simpleRewrite left right =
    RewriteRule $ rulePattern left right

runVerificationToPattern
    :: (NFData (Rule claim), Verification.Claim claim)
    => ProofState claim (Pattern Variable) ~ Verification.CommonProofState
    => Show claim
    => Show (Rule claim)
    => Limit Natural
    -> Limit Natural
    -> [Rule claim]
    -> [claim]
    -> IO (Either (Pattern Variable) ())
runVerificationToPattern breadthLimit depthLimit axioms claims = do
    stuck <- runVerification breadthLimit depthLimit axioms claims
    return (toPattern stuck)
  where
    toPattern (Left StuckVerification {stuckDescription}) = Left stuckDescription
    toPattern (Right a) = Right a


runVerification
    :: (NFData (Rule claim), Verification.Claim claim)
    => ProofState claim (Pattern Variable) ~ Verification.CommonProofState
    => Show claim
    => Show (Rule claim)
    => Limit Natural
    -> Limit Natural
    -> [Rule claim]
    -> [claim]
    -> IO (Either (StuckVerification (Pattern Variable) claim) ())
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
