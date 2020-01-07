{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}
module Kore.Step.Simplification.Rule
    ( simplifyRulePattern
    , simplifyRewriteRule
    , simplifyEqualityRule
    , simplifyFunctionAxioms
    ) where

import Data.Map.Strict
    ( Map
    )

import qualified Kore.Internal.Condition as Condition
    ( top
    )
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
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.EqualityPattern
    ( EqualityPattern (..)
    , EqualityRule (..)
    )
import Kore.Step.RulePattern
import qualified Kore.Step.Simplification.Pattern as Pattern
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , SimplifierVariable
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import qualified Kore.Unification.Substitution as Substitution

{- | Simplify a 'Map' of 'EqualityRule's using only matching logic rules.

See also: 'simplifyRulePattern'

 -}
simplifyFunctionAxioms
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => Map identifier [EqualityRule variable]
    -> simplifier (Map identifier [EqualityRule variable])
simplifyFunctionAxioms =
    (traverse . traverse) simplifyEqualityRule

simplifyEqualityRule
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => EqualityRule variable
    -> simplifier (EqualityRule variable)
simplifyEqualityRule (EqualityRule rule) =
    EqualityRule <$> simplifyEqualityPattern rule

{- | Simplify an 'EqualityPattern' using only matching logic rules.

The original rule is returned unless the simplification result matches certain
narrowly-defined criteria.

 -}
simplifyEqualityPattern
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => EqualityPattern variable
    -> simplifier (EqualityPattern variable)
simplifyEqualityPattern rule = do
    let EqualityPattern { left } = rule
    simplifiedLeft <- simplifyPattern left
    case OrPattern.toPatterns simplifiedLeft of
        [ Conditional { term, predicate, substitution } ]
          | PredicateTrue <- predicate -> do
            let subst = Substitution.toMap substitution
                left' = TermLike.substitute subst term
                requires' = TermLike.substitute subst <$> requires
                  where
                    EqualityPattern { requires = requires } = rule
                rhs' = TermLike.substitute subst rhs
                  where
                    EqualityPattern { right = rhs } = rule
                ensures' = TermLike.substitute subst <$> ensures
                  where
                    EqualityPattern { ensures = ensures } = rule
                EqualityPattern { attributes } = rule
            return EqualityPattern
                { left = left'
                , requires = requires'
                , right = rhs'
                , ensures = ensures'
                , attributes = attributes
                }
        _ ->
            -- Unable to simplify the given rule pattern, so we return the
            -- original pattern in the hope that we can do something with it
            -- later.
            return rule

{- | Simplify a 'Rule' using only matching logic rules.

See also: 'simplifyRulePattern'

 -}
simplifyRewriteRule
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => RewriteRule variable
    -> simplifier (RewriteRule variable)
simplifyRewriteRule (RewriteRule rule) =
    RewriteRule <$> simplifyRulePattern rule

{- | Simplify a 'RulePattern' using only matching logic rules.

The original rule is returned unless the simplification result matches certain
narrowly-defined criteria.

 -}
simplifyRulePattern
    :: (SimplifierVariable variable, MonadSimplify simplifier)
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
                antiLeft' = TermLike.substitute subst <$> antiLeft
                  where
                    RulePattern { antiLeft } = rule
                requires' = TermLike.substitute subst <$> requires
                  where
                    RulePattern { requires } = rule
                rhs' = rhsSubstitute subst rhs
                  where
                    RulePattern { rhs } = rule
                RulePattern { attributes } = rule
            return RulePattern
                { left = left'
                , antiLeft = antiLeft'
                , requires = requires'
                , rhs = rhs'
                , attributes = attributes
                }
        _ ->
            -- Unable to simplify the given rule pattern, so we return the
            -- original pattern in the hope that we can do something with it
            -- later.
            return rule

-- | Simplify a 'TermLike' using only matching logic rules.
simplifyPattern
    :: (SimplifierVariable variable, MonadSimplify simplifier)
    => TermLike variable
    -> simplifier (OrPattern variable)
simplifyPattern termLike =
    Simplifier.localSimplifierTermLike (const Simplifier.create)
    $ Simplifier.localSimplifierAxioms (const mempty)
    $ Pattern.simplify Condition.top (Pattern.fromTermLike termLike)
