{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Rewrite.Rule.Simplify (
    SimplifyRuleLHS (..),
    simplifyClaimPattern,
    simplifyRewriteRule,
    simplifyRulePattern,
) where

import qualified Kore.Internal.Condition as Condition
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    pattern PredicateTrue,
 )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Reachability (
    AllPathClaim (..),
    OnePathClaim (..),
    SomeClaim (..),
 )
import qualified Kore.Rewrite.AntiLeft as AntiLeft
import Kore.Rewrite.ClaimPattern (
    ClaimPattern (..),
 )
import qualified Kore.Rewrite.ClaimPattern as ClaimPattern
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Rewrite.RulePattern (
    RewriteRule (..),
    RulePattern (RulePattern),
 )
import qualified Kore.Rewrite.RulePattern as OLD
import qualified Kore.Rewrite.RulePattern as RulePattern (
    RulePattern (..),
    applySubstitution,
    rhsForgetSimplified,
 )
import qualified Kore.Rewrite.SMT.Evaluator as SMT.Evaluator
import qualified Kore.Simplify.Pattern as Pattern
import Kore.Simplify.Simplify (
    MonadSimplify,
 )
import qualified Kore.Simplify.Simplify as Simplifier
import Kore.Substitute (
    Substitute (..),
 )
import Logic (
    LogicT,
 )
import qualified Logic
import Prelude.Kore

-- | Simplifies the left-hand-side of a rewrite rule (claim or axiom)
class SimplifyRuleLHS rule where
    simplifyRuleLhs ::
        forall simplifier.
        MonadSimplify simplifier =>
        rule ->
        simplifier (MultiAnd rule)

instance SimplifyRuleLHS (RulePattern RewritingVariableName) where
    simplifyRuleLhs rule@(RulePattern _ _ _ _ _) = do
        let lhsWithPredicate = Pattern.fromTermLike left
        simplifiedTerms <-
            Pattern.simplifyTopConfiguration lhsWithPredicate
        fullySimplified <- SMT.Evaluator.filterMultiOr simplifiedTerms
        let rules = map (setRuleLeft rule) (toList fullySimplified)
        return (MultiAnd.make rules)
      where
        RulePattern{left} = rule

        setRuleLeft ::
            RulePattern RewritingVariableName ->
            Pattern RewritingVariableName ->
            RulePattern RewritingVariableName
        setRuleLeft
            rulePattern@RulePattern{requires = requires'}
            Conditional{term, predicate, substitution} =
                RulePattern.applySubstitution
                    substitution
                    rulePattern
                        { RulePattern.left = term
                        , RulePattern.requires =
                            makeAndPredicate predicate requires'
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

simplifyClaimRule ::
    forall simplifier.
    MonadSimplify simplifier =>
    ClaimPattern ->
    simplifier (MultiAnd ClaimPattern)
simplifyClaimRule claimPattern = fmap MultiAnd.make $
    Logic.observeAllT $ do
        let lhs = Pattern.requireDefined $ ClaimPattern.left claimPattern
        simplified <-
            Pattern.simplifyTopConfiguration lhs
                >>= Logic.scatter
                >>= filterWithSolver
        let substitution = Pattern.substitution simplified
            lhs' = simplified{Pattern.substitution = mempty}
        claimPattern{ClaimPattern.left = lhs'}
            & ClaimPattern.applySubstitution substitution
            & return
  where
    filterWithSolver ::
        Pattern RewritingVariableName ->
        LogicT simplifier (Pattern RewritingVariableName)
    filterWithSolver conditional =
        SMT.Evaluator.evalConditional conditional Nothing >>= \case
            Just False -> empty
            _ -> return conditional

{- | Simplify a 'Rule' using only matching logic rules.

See also: 'simplifyRulePattern'
-}
simplifyRewriteRule ::
    MonadSimplify simplifier =>
    RewriteRule RewritingVariableName ->
    simplifier (RewriteRule RewritingVariableName)
simplifyRewriteRule (RewriteRule rule) =
    RewriteRule <$> simplifyRulePattern rule

{- | Simplify a 'RulePattern' using only matching logic rules.

The original rule is returned unless the simplification result matches certain
narrowly-defined criteria.
-}
simplifyRulePattern ::
    MonadSimplify simplifier =>
    RulePattern RewritingVariableName ->
    simplifier (RulePattern RewritingVariableName)
simplifyRulePattern rule = do
    let RulePattern{left} = rule
    simplifiedLeft <- simplifyPattern' left
    case OrPattern.toPatterns simplifiedLeft of
        [Conditional{term, predicate, substitution}]
            | PredicateTrue <- predicate -> do
                -- TODO (virgil): Dropping the substitution for equations
                -- and for rewrite rules where the substituted variables occur
                -- in the RHS is wrong because those variables are not
                -- existentially quantified.
                let subst = Substitution.toMap substitution
                    left' = substitute subst term
                    antiLeft' = substitute subst <$> antiLeft
                      where
                        RulePattern{antiLeft} = rule
                    requires' = substitute subst requires
                      where
                        RulePattern{requires} = rule
                    rhs' = substitute subst rhs
                      where
                        RulePattern{rhs} = rule
                    RulePattern{attributes} = rule
                return
                    RulePattern
                        { left = TermLike.forgetSimplified left'
                        , antiLeft = AntiLeft.forgetSimplified <$> antiLeft'
                        , requires = Predicate.forgetSimplified requires'
                        , rhs = RulePattern.rhsForgetSimplified rhs'
                        , attributes = attributes
                        }
        _ ->
            -- Unable to simplify the given rule pattern, so we return the
            -- original pattern in the hope that we can do something with it
            -- later.
            return rule

{- | Simplify a 'ClaimPattern' using only matching logic rules.

The original rule is returned unless the simplification result matches certain
narrowly-defined criteria.
-}
simplifyClaimPattern ::
    MonadSimplify simplifier =>
    ClaimPattern ->
    simplifier ClaimPattern
simplifyClaimPattern claim = do
    let ClaimPattern{left} = claim
    simplifiedLeft <- simplifyPattern' (Pattern.term left)
    case OrPattern.toPatterns simplifiedLeft of
        [Conditional{term, predicate, substitution}]
            | PredicateTrue <- predicate ->
                -- TODO (virgil): Dropping the substitution for equations
                -- and for rewrite rules where the substituted variables occur
                -- in the RHS is wrong because those variables are not
                -- existentially quantified.
                let subst = Substitution.toMap substitution
                    left' = Pattern.withCondition term (Pattern.withoutTerm left)
                 in return
                        . ClaimPattern.forgetSimplified
                        . substitute subst
                        $ claim
                            { ClaimPattern.left = left'
                            }
        _ ->
            -- Unable to simplify the given claim pattern, so we return the
            -- original pattern in the hope that we can do something with it
            -- later.
            return claim

-- | Simplify a 'TermLike' using only matching logic rules.
simplifyPattern' ::
    MonadSimplify simplifier =>
    TermLike RewritingVariableName ->
    simplifier (OrPattern.OrPattern RewritingVariableName)
simplifyPattern' termLike =
    Simplifier.localSimplifierAxioms (const mempty) $
        Simplifier.simplifyPattern
            SideCondition.top
            (Pattern.fromTermLike termLike)
