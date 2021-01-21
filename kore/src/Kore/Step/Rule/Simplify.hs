{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Step.Rule.Simplify
    ( SimplifyRuleLHS (..)
    ) where

import Prelude.Kore

import Control.Monad
    ( (>=>)
    )

import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( makeAndPredicate
    )
import Kore.Reachability
    ( AllPathClaim (..)
    , OnePathClaim (..)
    , SomeClaim (..)
    )
import Kore.Rewriting.RewritingVariable
    ( RewritingVariableName
    )
import Kore.Step.ClaimPattern
    ( ClaimPattern (ClaimPattern)
    )
import qualified Kore.Step.ClaimPattern as ClaimPattern
import Kore.Step.RulePattern
    ( RewriteRule (..)
    , RulePattern (RulePattern)
    )
import qualified Kore.Step.RulePattern as OLD
import qualified Kore.Step.RulePattern as RulePattern
    ( RulePattern (..)
    , applySubstitution
    )
import qualified Kore.Step.Simplification.Pattern as Pattern
import Kore.Step.Simplification.Simplify
    ( InternalVariable
    , MonadSimplify
    )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
import Logic
    ( LogicT
    )
import qualified Logic

-- | Simplifies the left-hand-side of a rewrite rule (claim or axiom)
class SimplifyRuleLHS rule where
    simplifyRuleLhs
        :: forall simplifier
        .  MonadSimplify simplifier
        => rule
        -> simplifier (MultiAnd rule)

instance SimplifyRuleLHS (RulePattern RewritingVariableName)
  where
    simplifyRuleLhs rule@(RulePattern _ _ _ _ _) = do
        let lhsWithPredicate = Pattern.fromTermLike left
        simplifiedTerms <-
            Pattern.simplifyTopConfiguration lhsWithPredicate
        fullySimplified <- SMT.Evaluator.filterMultiOr simplifiedTerms
        let rules = map (setRuleLeft rule) (toList fullySimplified)
        return (MultiAnd.make rules)
      where
        RulePattern {left} = rule

        setRuleLeft
            :: InternalVariable variable
            => RulePattern variable
            -> Pattern variable
            -> RulePattern variable
        setRuleLeft
            rulePattern@RulePattern {requires = requires'}
            Conditional {term, predicate, substitution}
          =
            RulePattern.applySubstitution
                substitution
                rulePattern
                    { RulePattern.left = term
                    , RulePattern.requires =
                        makeAndPredicate predicate requires'
                    }

instance SimplifyRuleLHS ClaimPattern
  where
    simplifyRuleLhs rule@(ClaimPattern _ _ _ _) = do
        simplifiedTerms <-
            Pattern.simplifyTopConfiguration left
        fullySimplified <-
            SMT.Evaluator.filterMultiOr simplifiedTerms
        let rules =
                setRuleLeft rule
                <$> OrPattern.toPatterns fullySimplified
        return (MultiAnd.make rules)
      where
        ClaimPattern { left } = rule

        setRuleLeft
            :: ClaimPattern
            -> Pattern RewritingVariableName
            -> ClaimPattern
        setRuleLeft
            claimPattern@ClaimPattern { left = left' }
            patt@Conditional { substitution }
          =
            ClaimPattern.applySubstitution
                substitution
                claimPattern
                    { ClaimPattern.left =
                        Condition.andCondition
                            patt
                            (Condition.eraseConditionalTerm left')
                    }

instance SimplifyRuleLHS (RewriteRule RewritingVariableName) where
    simplifyRuleLhs =
        fmap (MultiAnd.map RewriteRule)
        . simplifyRuleLhs
        . getRewriteRule

instance SimplifyRuleLHS OnePathClaim where
    simplifyRuleLhs =
        fmap (MultiAnd.map OnePathClaim)
        . simplifyClaimRule
        . getOnePathClaim

instance SimplifyRuleLHS AllPathClaim where
    simplifyRuleLhs =
        fmap (MultiAnd.map AllPathClaim)
        . simplifyClaimRule
        . getAllPathClaim

instance SimplifyRuleLHS SomeClaim where
    simplifyRuleLhs (OnePath rule) =
        (fmap . MultiAnd.map) OnePath $ simplifyRuleLhs rule
    simplifyRuleLhs (AllPath rule) =
        (fmap . MultiAnd.map) AllPath $ simplifyRuleLhs rule

simplifyClaimRule
    :: forall simplifier
    .  MonadSimplify simplifier
    => ClaimPattern
    -> simplifier (MultiAnd ClaimPattern)
simplifyClaimRule =
    fmap MultiAnd.make . Logic.observeAllT . worker
  where
    simplify, filterWithSolver
        :: Pattern RewritingVariableName
        -> LogicT simplifier (Pattern RewritingVariableName)
    simplify =
        (return . Pattern.requireDefined)
        >=> Pattern.simplifyTopConfiguration
        >=> Logic.scatter
        >=> filterWithSolver
    filterWithSolver = SMT.Evaluator.filterBranch

    worker :: ClaimPattern -> LogicT simplifier ClaimPattern
    worker claimPattern = do
        let lhs = ClaimPattern.left claimPattern
        simplified <- simplify lhs
        let substitution = Pattern.substitution simplified
            lhs' = simplified { Pattern.substitution = mempty }
        claimPattern
            { ClaimPattern.left = lhs'
            }
            & ClaimPattern.applySubstitution substitution
            & return
