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

import Prelude.Kore

import Data.Map.Strict
    ( Map
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
import qualified Kore.Internal.SideCondition as SideCondition
    ( topTODO
    )
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Step.EqualityPattern
    ( EqualityRule (..)
    )
import Kore.Step.RulePattern
import qualified Kore.Step.Simplification.Pattern as Pattern
import qualified Kore.Step.Simplification.Simplifier as Simplifier
import Kore.Step.Simplification.Simplify
    ( InternalVariable
    , MonadSimplify
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier

{- | Simplify a 'Map' of 'EqualityRule's using only matching logic rules.

See also: 'simplifyRulePattern'

 -}
simplifyFunctionAxioms
    :: (InternalVariable variable, MonadSimplify simplifier)
    => Map identifier [EqualityRule variable]
    -> simplifier (Map identifier [EqualityRule variable])
simplifyFunctionAxioms =
    (traverse . traverse) simplifyEqualityRule

{- | Simplify an 'EqualityPattern' using only matching logic rules.

The original rule is returned unless the simplification result matches certain
narrowly-defined criteria.

 -}
simplifyEqualityRule
    :: (InternalVariable variable, MonadSimplify simplifier)
    => EqualityRule variable
    -> simplifier (EqualityRule variable)
simplifyEqualityRule rule = do
    let EqualityRule { left } = rule
    simplifiedLeft <- simplifyPattern left
    case OrPattern.toPatterns simplifiedLeft of
        [ Conditional { term, predicate, substitution } ]
          | PredicateTrue <- predicate -> do
            let subst = Substitution.toMap substitution
                left' = TermLike.substitute subst term
                requires' = TermLike.substitute subst <$> requires
                  where
                    EqualityRule { requires = requires } = rule
                rhs' = TermLike.substitute subst rhs
                  where
                    EqualityRule { right = rhs } = rule
                ensures' = TermLike.substitute subst <$> ensures
                  where
                    EqualityRule { ensures = ensures } = rule
                EqualityRule { attributes } = rule
            return EqualityRule
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
    :: (InternalVariable variable, MonadSimplify simplifier)
    => TermLike variable
    -> simplifier (OrPattern variable)
simplifyPattern termLike =
    Simplifier.localSimplifierTermLike (const Simplifier.create)
    $ Simplifier.localSimplifierAxioms (const mempty)
    $ Pattern.simplify SideCondition.topTODO (Pattern.fromTermLike termLike)
