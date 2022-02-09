{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Simplify.FunctionEvaluator (

) where

import Prelude.Kore
import Kore.Attribute.Synthetic (synthesize)
import qualified Kore.Internal.Pattern as Pattern
import Kore.Simplify.Simplify
import Control.Monad.Trans.Maybe (MaybeT (..))
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.TermLike (TermLike)
import qualified Kore.Internal.TermLike as TermLike
import Control.Monad.Except (
    ExceptT (..),
    runExceptT,
 )
import Data.EitherR (
    ExceptRT (..),
 )
import Data.Semigroup (
    Min (..),
    Option (..),
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Internal.Pattern (Pattern)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Kore.Equation as Equation
import Kore.Equation.DebugEquation (
    AttemptEquationError,
 )
import Kore.Rewrite.Axiom.Identifier (AxiomIdentifier, matchAxiomIdentifier)
import Kore.Equation.Equation (Equation)
import qualified Data.Functor.Foldable as Recursive

evaluateFunctions ::
    forall simplifier .
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Map AxiomIdentifier [Equation RewritingVariableName] ->
    TermLike RewritingVariableName ->
    simplifier (Pattern RewritingVariableName)
evaluateFunctions sideCondition equations termLike =
    loop . Pattern.fromTermLike $ termLike
  where

    loop ::
        Pattern RewritingVariableName ->
        simplifier (Pattern RewritingVariableName)
    loop input = do
        -- Basically I'd like a monad instance here, but it would be inefficient
        output <- traverse worker input
        if input == output
            then pure output
            else loop output

    worker ::
        TermLike RewritingVariableName ->
        simplifier (Pattern RewritingVariableName)
    worker = Recursive.cata f

    f ::
        Recursive.Base
            (TermLike RewritingVariableName)
            (simplifier (Pattern RewritingVariableName)) ->
        simplifier (Pattern RewritingVariableName)
    f termLikeBase = do
        let _ :< termLikeF = termLikeBase
        case termLikeF of
            TermLike.ApplySymbolF applySymbol -> do
                let TermLike.Application
                            { applicationSymbolOrAlias
                            , applicationChildren
                            } = applySymbol
                childrenResults <- sequence applicationChildren
                let childrenTerms = extract <$> childrenResults
                    childrenCondition = fold $ Pattern.withoutTerm <$> childrenResults
                let newApplication =
                        TermLike.Application applicationSymbolOrAlias childrenTerms
                        -- should use old attributes here?
                        & TermLike.ApplySymbolF
                        & synthesize
                result <-
                    evaluateFunction sideCondition equations newApplication
                    & runMaybeT
                case result of
                    Just simplifiedApplication ->
                        Pattern.andCondition
                            simplifiedApplication
                            childrenCondition
                            & return
                    Nothing ->
                        Pattern.withCondition
                            newApplication
                            childrenCondition
                            & return
            _ -> do
                x <- sequence termLikeBase
                let y = Recursive.embed $ extract <$> x
                    z =
                        Pattern.withoutTerm <$> x
                        & fold
                return (Pattern.withCondition y z)


evaluateFunction ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Map AxiomIdentifier [Equation RewritingVariableName] ->
    TermLike RewritingVariableName ->
    MaybeT simplifier (Pattern RewritingVariableName)
evaluateFunction sideCondition equations termLike = do
    identifier <- MaybeT . return $ matchAxiomIdentifier termLike
    possibleMatches <- MaybeT . return $ Map.lookup identifier equations
    result <-
        attemptEquations
            (attemptEquationAndAccumulateErrors sideCondition termLike)
            possibleMatches
    case result of
        Right newPattern ->
            return newPattern
        Left _ ->
            empty

attemptEquationAndAccumulateErrors ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    TermLike RewritingVariableName ->
    Equation RewritingVariableName ->
    ExceptRT
        (Pattern RewritingVariableName)
        simplifier
        (Option (Min (AttemptEquationError RewritingVariableName)))
attemptEquationAndAccumulateErrors condition term equation =
    attemptEquation
  where
    attemptEquation =
        ExceptRT . ExceptT $
            Equation.attemptEquation
                condition
                term
                equation
                >>= either (return . Left . Option . Just . Min) (fmap Right . apply)
    apply = Equation.applyEquationTODO condition equation

attemptEquations ::
    MonadSimplify simplifier =>
    Monoid error =>
    (Equation variable -> ExceptRT result simplifier error) ->
    [Equation variable] ->
    simplifier (Either error result)
attemptEquations accumulator equations =
    foldlM
        (\err equation -> mappend err <$> accumulator equation)
        mempty
        equations
        & runExceptRT
        & runExceptT


-- n - length of term
-- m - no. of equations to try
--
-- for each subterm in term
--   find equations with id subterm -- map lookup
--   attempt equations --
