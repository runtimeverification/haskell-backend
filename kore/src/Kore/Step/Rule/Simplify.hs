{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Step.Rule.Simplify
    ( simplifyOnePathRuleLhs
    ) where

import qualified Branch as BranchT
    ( gather
    , scatter
    )
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
    ( Conditional (..)
    )
import qualified Kore.Internal.Conditional as Conditional
    ( withCondition
    )
import qualified Kore.Internal.Predicate as Predicate
    ( fromPredicate
    )
import Kore.Step.Rule
    ( OnePathRule (..)
    , RulePattern (RulePattern)
    )
import qualified Kore.Step.Rule as RulePattern
    ( RulePattern (..)
    , applySubstitution
    )
import qualified Kore.Step.Simplification.Pattern as Pattern
    ( simplifyAndRemoveTopExists
    )
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , SimplifierVariable
    )

simplifyOnePathRuleLhs
    ::  ( MonadSimplify simplifier
        , SimplifierVariable variable
        )
    => OnePathRule variable
    -> simplifier [OnePathRule variable]
simplifyOnePathRuleLhs (OnePathRule rule) = do
    simplifiedList <- simplifyRuleLhs rule
    return (map OnePathRule simplifiedList)

simplifyRuleLhs
    ::  ( MonadSimplify simplifier
        , SimplifierVariable variable
        )
    => RulePattern variable
    -> simplifier [RulePattern variable]
simplifyRuleLhs rule@(RulePattern _ _ _ _ _ _) = do
    simplified <- Pattern.simplifyAndRemoveTopExists
        (left `Conditional.withCondition` Predicate.fromPredicate requires)
    BranchT.gather $ do
        Conditional {term, predicate, substitution} <-
            BranchT.scatter simplified
        let finalRule =
                RulePattern.applySubstitution
                    substitution
                    rule
                        { RulePattern.left = term
                        , RulePattern.requires = predicate
                        }
        return finalRule
  where
    RulePattern {left, requires} = rule

