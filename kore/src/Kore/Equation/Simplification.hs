{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}

module Kore.Equation.Simplification
    ( simplifyEquation
    , simplifyExtractedEquations
    ) where

import Prelude.Kore

import Control.Error
    ( maybeT
    )
import qualified Control.Monad as Monad
import Data.Map.Strict
    ( Map
    )

import Kore.Equation.Equation
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.Substitution as Substitution
import Kore.Internal.TermLike
    ( TermLike
    )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Step.Simplification.Pattern as Pattern
import Kore.Step.Simplification.Simplify
    ( InternalVariable
    , MonadSimplify
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import Kore.TopBottom

{- | Simplify a 'Map' of 'EqualityRule's using only Matching Logic rules.

See also: 'Kore.Equation.Registry.extractEquations'

 -}
simplifyExtractedEquations
    :: (InternalVariable variable, MonadSimplify simplifier)
    => Map identifier [Equation variable]
    -> simplifier (Map identifier [Equation variable])
simplifyExtractedEquations =
    (traverse . traverse) simplifyEquation

{- | Simplify an 'Equation' using only Matching Logic rules.

The original rule is returned unless the simplification result matches certain
narrowly-defined criteria.

 -}
simplifyEquation
    :: (InternalVariable variable, MonadSimplify simplifier)
    => Equation variable
    -> simplifier (Equation variable)
simplifyEquation equation@(Equation _ _ _ _ _ _ _) =
    do
        let Equation
                { requires
                , argument
                , antiLeft
                , left
                , right
                , ensures
                , attributes } = equation
        simplified <- simplifyTermLike left >>= expectSingleResult
        let Conditional { term, predicate, substitution } = simplified
        Monad.guard (isTop predicate)
        let subst = Substitution.toMap substitution
            left' = TermLike.substitute subst term
            requires' = TermLike.substitute subst <$> requires
            argument' = (fmap . fmap) (TermLike.substitute subst) argument
            antiLeft' = (fmap . fmap) (TermLike.substitute subst) antiLeft
            right' = TermLike.substitute subst right
            ensures' = TermLike.substitute subst <$> ensures
        return Equation
            { left = TermLike.forgetSimplified left'
            , requires = Predicate.forgetSimplified requires'
            , argument = Predicate.forgetSimplified <$> argument'
            , antiLeft = Predicate.forgetSimplified <$> antiLeft'
            , right = TermLike.forgetSimplified right'
            , ensures = Predicate.forgetSimplified ensures'
            , attributes = attributes
            }
    -- Unable to simplify the given equation, so we return the original equation
    -- in the hope that we can do something with it later.
    & fromMaybeT (return equation)
  where
    fromMaybeT = flip maybeT return
    expectSingleResult results =
        case OrPattern.toPatterns results of
            [result] -> return result
            _        -> empty

-- | Simplify a 'TermLike' using only matching logic rules.
simplifyTermLike
    :: (InternalVariable variable, MonadSimplify simplifier)
    => TermLike variable
    -> simplifier (OrPattern variable)
simplifyTermLike termLike =
    Simplifier.localSimplifierAxioms (const mempty)
    $ Pattern.simplify (Pattern.fromTermLike termLike)
