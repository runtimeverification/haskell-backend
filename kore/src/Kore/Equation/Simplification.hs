{- |
Copyright   : (c) Runtime Verification, 2020
License     : NCSA

-}
{-# LANGUAGE Strict #-}

module Kore.Equation.Simplification
    ( simplifyEquation
    , simplifyExtractedEquations
    ) where

import Prelude.Kore

import qualified Control.Monad as Monad
import Control.Monad.Trans.Except
    ( runExceptT
    , throwE
    )
import Data.Map.Strict
    ( Map
    )

import Kore.Equation.Equation
import Kore.Internal.Conditional
    ( Conditional (..)
    )
import Kore.Internal.MultiAnd
    ( MultiAnd
    )
import qualified Kore.Internal.MultiAnd as MultiAnd
import Kore.Internal.OrPattern
    ( OrPattern
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition as SideCondition
    ( top
    )
import qualified Kore.Internal.Substitution as Substitution
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Step.Simplification.Pattern as Pattern
import Kore.Step.Simplification.Simplify
    ( InternalVariable
    , MonadSimplify
    )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import Kore.TopBottom
import qualified Logic

{- | Simplify a 'Map' of 'Equation's using only Matching Logic rules.

See also: 'Kore.Equation.Registry.extractEquations'

 -}
simplifyExtractedEquations
    :: (InternalVariable variable, MonadSimplify simplifier)
    => Map identifier [Equation variable]
    -> simplifier (Map identifier [Equation variable])
simplifyExtractedEquations = do
    results <- (traverse . traverse) simplifyEquation
    return $ collectResults results
  where
    collectResults = (fmap . fmap) (concatMap toList)

{- | Simplify an 'Equation' using only Matching Logic rules.

It attempts to unify the argument of the equation, creating new
equations where the argument is substituted in the rest of the
resulting equations, and the argument is removed.

If any of the patterns resulting from simplifying the term and the
argument contain a predicate which is not 'Top', 'simplifyEquation'
returns the original equation.

 -}
simplifyEquation
    :: (InternalVariable variable, MonadSimplify simplifier)
    => Equation variable
    -> simplifier (MultiAnd (Equation variable))
simplifyEquation equation@(Equation _ _ _ _ _ _ _) =
    do
        simplifiedResults <-
            simplifyPattern leftWithArgument
        Monad.when
            (any (not . isTop . predicate) simplifiedResults)
            (throwE equation)
        simplified <- lift $ Logic.scatter simplifiedResults
        let Conditional { term, predicate, substitution } = simplified
        Monad.unless (isTop predicate) (throwE equation)
        let subst = Substitution.toMap substitution
            left' = TermLike.substitute subst term
            requires' = Predicate.substitute subst requires
            antiLeft' = Predicate.substitute subst <$> antiLeft
            right' = TermLike.substitute subst right
            ensures' = Predicate.substitute subst ensures
        return Equation
            { left = TermLike.forgetSimplified left'
            , requires = Predicate.forgetSimplified requires'
            , argument = Nothing
            , antiLeft = Predicate.forgetSimplified <$> antiLeft'
            , right = TermLike.forgetSimplified right'
            , ensures = Predicate.forgetSimplified ensures'
            , attributes = attributes
            }
    & returnOriginalIfAborted
    & Logic.observeAllT
    & fmap MultiAnd.make
  where
    leftWithArgument =
        maybe
            (Pattern.fromTermLike left)
            (Pattern.fromTermAndPredicate left)
            argument
    returnOriginalIfAborted =
        fmap (either id id) . runExceptT
    Equation
        { requires
        , argument
        , antiLeft
        , left
        , right
        , ensures
        , attributes
        } = equation

-- | Simplify a 'Pattern' using only matching logic rules.
simplifyPattern
    :: (InternalVariable variable, MonadSimplify simplifier)
    => Pattern variable
    -> simplifier (OrPattern variable)
simplifyPattern patt =
    Simplifier.localSimplifierAxioms (const mempty)
    $ Pattern.simplify SideCondition.top patt
