{-# LANGUAGE TemplateHaskell #-}

{- |
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
-}
module Kore.Rewrite.Rule.Simplify (
    SimplifyRuleLHS (..),
    simplifyClaimPattern,
) where

import Kore.Internal.Condition qualified as Condition
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import Kore.Internal.MultiAnd qualified as MultiAnd
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.Pattern (
    Pattern,
 )
import Kore.Internal.Pattern qualified as Pattern
import Kore.Internal.Predicate (
    makeAndPredicate,
    pattern PredicateTrue,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.Substitution qualified as Substitution
import Kore.Internal.TermLike as TermLike
import Kore.Log.DecidePredicateUnknown (
    OnDecidePredicateUnknown (ErrorDecidePredicateUnknown),
    srcLoc,
 )
import Kore.Reachability (
    AllPathClaim (..),
    OnePathClaim (..),
    SomeClaim (..),
 )
import Kore.Rewrite.ClaimPattern (
    ClaimPattern (..),
 )
import Kore.Rewrite.ClaimPattern qualified as ClaimPattern
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Rewrite.RulePattern (
    RewriteRule (..),
    RulePattern (RulePattern),
 )
import Kore.Rewrite.RulePattern qualified as RulePattern (
    RulePattern (..),
    applySubstitution,
 )
import Kore.Rewrite.SMT.Evaluator qualified as SMT.Evaluator
import Kore.Simplify.Pattern qualified as Pattern
import Kore.Simplify.Simplify (
    Simplifier,
 )
import Kore.Simplify.Simplify qualified as Simplifier
import Kore.Substitute (
    Substitute (..),
 )
import Logic (
    LogicT,
 )
import Logic qualified
import Prelude.Kore

-- | Simplifies the left-hand-side of a rewrite rule (claim or axiom)
class SimplifyRuleLHS rule where
    simplifyRuleLhs :: rule -> Simplifier (MultiAnd rule)

instance SimplifyRuleLHS (RulePattern RewritingVariableName) where
    simplifyRuleLhs rule@RulePattern{left = And_ _ _ (ElemVar_ _)} = return $ MultiAnd.make [rule]
    simplifyRuleLhs rule = do
        let lhsWithPredicate = Pattern.fromTermLike left
        simplifiedTerms <-
            Pattern.simplifyTopConfiguration lhsWithPredicate
        fullySimplified <- SMT.Evaluator.filterMultiOr $srcLoc simplifiedTerms
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
    ClaimPattern ->
    Simplifier (MultiAnd ClaimPattern)
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
        LogicT Simplifier (Pattern RewritingVariableName)
    filterWithSolver conditional = do
        l <- lift $ SMT.Evaluator.evalConditional (ErrorDecidePredicateUnknown $srcLoc Nothing) conditional Nothing
        case l of
            Just False -> empty
            _ -> return conditional

{- | Simplify a 'ClaimPattern' using only matching logic rules.

The original rule is returned unless the simplification result matches certain
narrowly-defined criteria.
-}
simplifyClaimPattern ::
    ClaimPattern ->
    Simplifier ClaimPattern
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
    TermLike RewritingVariableName ->
    Simplifier (OrPattern.OrPattern RewritingVariableName)
simplifyPattern' termLike =
    Simplifier.localAxiomEquations (const mempty) $
        Simplifier.simplifyPattern
            SideCondition.top
            (Pattern.fromTermLike termLike)
