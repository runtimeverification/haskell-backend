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

import Data.Map
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
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import Kore.Predicate.Predicate
    ( pattern PredicateTrue
    )
import Kore.Step.Rule
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
    EqualityRule <$> simplifyRulePattern rule

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
            let subst = Substitution.toMap substitution
                left' = TermLike.substitute subst term
                antiLeft' = TermLike.substitute subst <$> antiLeft
                  where
                    RulePattern { antiLeft } = rule
                right' = TermLike.substitute subst right
                  where
                    RulePattern { right } = rule
                requires' = TermLike.substitute subst <$> requires
                  where
                    RulePattern { requires } = rule
                ensures' = TermLike.substitute subst <$> ensures
                  where
                    RulePattern { ensures } = rule
                RulePattern { attributes } = rule
            return RulePattern
                { left = left'
                , antiLeft = antiLeft'
                , right = right'
                , requires = requires'
                , ensures = ensures'
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
    $ Pattern.simplify (Pattern.fromTermLike termLike)
