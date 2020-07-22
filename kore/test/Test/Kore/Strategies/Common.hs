module Test.Kore.Strategies.Common
    ( simpleRewrite
    , runVerification
    , runVerificationToPattern
    ) where

import Prelude.Kore

import Control.Monad.Trans.Except
    ( runExceptT
    )
import qualified Data.Bifunctor as Bifunctor
import Data.Limit
    ( Limit (..)
    )
import Numeric.Natural
    ( Natural
    )

import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.TermLike
import Kore.Rewriting.RewritingVariable
import Kore.Step.RulePattern
    ( rulePattern
    )
import Kore.Step.SMT.Declaration.All as SMT.AST
import Kore.Step.Strategy
    ( GraphSearchOrder (..)
    )
import Kore.Strategies.Goal
import Kore.Strategies.Verification
    ( AllClaims (AllClaims)
    , AlreadyProven (AlreadyProven)
    , Axioms (Axioms)
    , Stuck (..)
    , ToProve (ToProve)
    )
import qualified Kore.Strategies.Verification as Verification
import Kore.Unparser
    ( unparseToText2
    )

import qualified Test.Kore.Step.MockSymbols as Mock
import Test.Kore.Step.Simplification

simpleRewrite
    :: TermLike VariableName
    -> TermLike VariableName
    -> RewriteRule RewritingVariableName
simpleRewrite left right =
    mkRewritingRule $ RewriteRule $ rulePattern left right

runVerificationToPattern
    :: Limit Natural
    -> Limit Natural
    -> [Rule ReachabilityRule]
    -> [ReachabilityRule]
    -> [ReachabilityRule]
    -> IO (Either (OrPattern VariableName) ())
runVerificationToPattern breadthLimit depthLimit axioms claims alreadyProven =
    do
        stuck <- runVerification
            breadthLimit
            depthLimit
            axioms
            claims
            alreadyProven
        return (toPattern stuck)
  where
    toPattern =
        Bifunctor.first stuckPatterns

runVerification
    :: Limit Natural
    -> Limit Natural
    -> [Rule ReachabilityRule]
    -> [ReachabilityRule]
    -> [ReachabilityRule]
    -> IO (Either Stuck ())
runVerification breadthLimit depthLimit axioms claims alreadyProven =
    runSimplifier mockEnv $ do
        SMT.AST.declare Mock.smtDeclarations
        runExceptT
            $ Verification.verify
                breadthLimit
                BreadthFirst
                (AllClaims claims)
                (Axioms axioms)
                (AlreadyProven (map unparseToText2 alreadyProven))
                (ToProve (map applyDepthLimit . selectUntrusted $ claims))
  where
    mockEnv = Mock.env
    applyDepthLimit claim = (claim, depthLimit)
    selectUntrusted = filter (not . isTrusted)
