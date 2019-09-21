module Test.Kore.Strategies.Common where

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
    -> [Rule claim]
    -> [claim]
    -> IO (Either (Pattern Variable) ())
runVerification stepLimit axioms claims =
    runSimplifier mockEnv
    $ runExceptT
    $ Verification.verify
        (strategy claims axioms)
        (map applyStepLimit . selectUntrusted $ claims)
  where
    mockEnv = Mock.env
    applyStepLimit claim = (claim, stepLimit)
    selectUntrusted = filter (not . isTrusted)
