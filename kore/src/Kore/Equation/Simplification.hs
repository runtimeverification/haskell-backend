{- |
Copyright   : (c) Runtime Verification, 2020
License     : BSD-3-Clause
-}
module Kore.Equation.Simplification (
    simplifyEquation,
    simplifyExtractedEquations,
) where

import qualified Control.Monad as Monad
import Control.Monad.Trans.Except (
    runExceptT,
    throwE,
 )
import Data.Map.Strict (
    Map,
 )
import Kore.Equation.Equation
import Kore.Internal.Conditional (
    Conditional (..),
    fromPredicate,
 )
import Kore.Internal.MultiAnd (
    MultiAnd,
 )
import qualified Kore.Internal.MultiAnd as MultiAnd
import qualified Kore.Internal.Predicate as Predicate
import qualified Kore.Internal.SideCondition as SideCondition
import qualified Kore.Internal.Substitution as Substitution
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Simplification.Simplify (
    MonadSimplify,
 )
import qualified Kore.Step.Simplification.Simplify as Simplifier
import Kore.Substitute
import Kore.TopBottom
import qualified Logic
import Prelude.Kore

{- | Simplify a 'Map' of 'Equation's using only Matching Logic rules.

See also: 'Kore.Equation.Registry.extractEquations'
-}
simplifyExtractedEquations ::
    MonadSimplify simplifier =>
    Map identifier [Equation RewritingVariableName] ->
    simplifier (Map identifier [Equation RewritingVariableName])
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
simplifyEquation ::
    MonadSimplify simplifier =>
    Equation RewritingVariableName ->
    simplifier (MultiAnd (Equation RewritingVariableName))
simplifyEquation equation@(Equation _ _ _ _ _ _ _) =
    do
        simplifiedCond <-
            Simplifier.simplifyCondition
                SideCondition.top
                (fromPredicate argument')
        let Conditional{substitution, predicate} = simplifiedCond
        lift $ Monad.unless (isTop predicate) (throwE equation)
        let subst = Substitution.toMap substitution
            left' = substitute subst left
            requires' = substitute subst requires
            antiLeft' = substitute subst <$> antiLeft
            right' = substitute subst right
            ensures' = substitute subst ensures
        return
            Equation
                { left = TermLike.forgetSimplified left'
                , requires = Predicate.forgetSimplified requires'
                , argument = Nothing
                , antiLeft = Predicate.forgetSimplified <$> antiLeft'
                , right = TermLike.forgetSimplified right'
                , ensures = Predicate.forgetSimplified ensures'
                , attributes = attributes
                }
        & Logic.observeAllT
        & returnOriginalIfAborted
        & fmap MultiAnd.make
  where
    argument' =
        fromMaybe Predicate.makeTruePredicate argument
    returnOriginalIfAborted =
        fmap (either (: []) id) . runExceptT
    Equation
        { requires
        , argument
        , antiLeft
        , left
        , right
        , ensures
        , attributes
        } = equation
