{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Step.Simplification.Rule
    ( simplifyRulePattern
    , simplifyRewriteRule
    , simplifyClaimPattern
    ) where

import Prelude.Kore

import Kore.Internal.Conditional
    ( Conditional (..)
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( pattern PredicateTrue
    )
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Step.AntiLeft as AntiLeft
    ( forgetSimplified
    , substitute
    )
import Kore.Step.ClaimPattern
    ( ClaimPattern (..)
    )
import qualified Kore.Step.ClaimPattern as ClaimPattern
import Kore.Step.RulePattern
import qualified Kore.Step.Simplification.Pattern as Pattern
import Kore.Step.Simplification.Simplify
    ( InternalVariable
    , MonadSimplify
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier

{- | Simplify a 'Rule' using only matching logic rules.

See also: 'simplifyRulePattern'

 -}
simplifyRewriteRule
    :: (InternalVariable variable, MonadSimplify simplifier)
    => RewriteRule variable
    -> simplifier (RewriteRule variable)
simplifyRewriteRule (RewriteRule rule) =
    RewriteRule <$> simplifyRulePattern rule

{- | Simplify a 'RulePattern' using only matching logic rules.

The original rule is returned unless the simplification result matches certain
narrowly-defined criteria.

 -}
simplifyRulePattern
    :: (InternalVariable variable, MonadSimplify simplifier)
    => RulePattern variable
    -> simplifier (RulePattern variable)
simplifyRulePattern rule = do
    let RulePattern { left } = rule
    simplifiedLeft <- simplifyPattern left
    case OrPattern.toPatterns simplifiedLeft of
        [ Conditional { term, predicate, substitution } ]
          | PredicateTrue <- predicate -> do
            -- TODO (virgil): Dropping the substitution for equations
            -- and for rewrite rules where the substituted variables occur
            -- in the RHS is wrong because those variables are not
            -- existentially quantified.
            let subst = Substitution.toMap substitution
                left' = TermLike.substitute subst term
                antiLeft' = AntiLeft.substitute subst <$> antiLeft
                  where
                    RulePattern { antiLeft } = rule
                requires' = Predicate.substitute subst requires
                  where
                    RulePattern { requires } = rule
                rhs' = rhsSubstitute subst rhs
                  where
                    RulePattern { rhs } = rule
                RulePattern { attributes } = rule
            return RulePattern
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
simplifyClaimPattern
    :: MonadSimplify simplifier
    => ClaimPattern
    -> simplifier ClaimPattern
simplifyClaimPattern claim = do
    let ClaimPattern { left } = claim
    simplifiedLeft <- simplifyPattern (Pattern.term left)
    case OrPattern.toPatterns simplifiedLeft of
        [ Conditional { term, predicate, substitution } ]
          | PredicateTrue <- predicate ->
            -- TODO (virgil): Dropping the substitution for equations
            -- and for rewrite rules where the substituted variables occur
            -- in the RHS is wrong because those variables are not
            -- existentially quantified.
            let subst = Substitution.toMap substitution
                left' = Pattern.withCondition term (Pattern.withoutTerm left)
             in return
                . ClaimPattern.forgetSimplified
                . ClaimPattern.substitute subst
                $ claim
                    { ClaimPattern.left = left'
                    }
        _ ->
            -- Unable to simplify the given claim pattern, so we return the
            -- original pattern in the hope that we can do something with it
            -- later.
            return claim

-- | Simplify a 'TermLike' using only matching logic rules.
simplifyPattern
    :: (InternalVariable variable, MonadSimplify simplifier)
    => TermLike variable
    -> simplifier (OrPattern variable)
simplifyPattern termLike =
    Simplifier.localSimplifierAxioms (const mempty)
    $ Pattern.simplify (Pattern.fromTermLike termLike)
