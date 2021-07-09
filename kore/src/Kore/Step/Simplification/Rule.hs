{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Step.Simplification.Rule (
    simplifyRulePattern,
    simplifyRewriteRule,
    simplifyClaimPattern,
) where

import Kore.Internal.Conditional (
    Conditional (..),
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate (
    pattern PredicateTrue,
 )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike (
    TermLike,
 )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Step.AntiLeft as AntiLeft
import Kore.Step.ClaimPattern (
    ClaimPattern (..),
 )
import qualified Kore.Step.ClaimPattern as ClaimPattern
import Kore.Step.RulePattern
import qualified Kore.Step.Simplification.Pattern as Pattern
import Kore.Step.Simplification.Simplify (
    MonadSimplify,
 )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import Kore.Substitute
import Prelude.Kore

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
    simplifiedLeft <- simplifyPattern left
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
                        , rhs = rhsForgetSimplified rhs'
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
    simplifiedLeft <- simplifyPattern (Pattern.term left)
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
simplifyPattern ::
    MonadSimplify simplifier =>
    TermLike RewritingVariableName ->
    simplifier (OrPattern RewritingVariableName)
simplifyPattern termLike =
    Simplifier.localSimplifierAxioms (const mempty) $
        Pattern.simplify (Pattern.fromTermLike termLike)
