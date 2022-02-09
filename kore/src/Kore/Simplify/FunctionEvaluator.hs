{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Simplify.FunctionEvaluator (
    evaluateFunctions,
) where

import Control.Monad.Except (
    ExceptT (..),
    runExceptT,
 )
import Control.Monad.Trans.Maybe (MaybeT (..))
import Control.Monad.Trans.Writer.Strict (WriterT (..))
import qualified Control.Monad.Trans.Writer.Strict as Writer
import Data.EitherR (
    ExceptRT (..),
 )
import qualified Data.Functor.Foldable as Recursive
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Semigroup (
    Min (..),
    Option (..),
 )
import qualified Kore.Equation as Equation
import Kore.Equation.DebugEquation (
    AttemptEquationError,
 )
import Kore.Equation.Equation (Equation)
import Kore.Internal.Pattern (Condition, Pattern)
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.TermLike (TermLike)
import qualified Kore.Internal.TermLike as TermLike
import Kore.Rewrite.Axiom.Identifier (AxiomIdentifier, matchAxiomIdentifier)
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify
import Prelude.Kore

type FunctionEvaluator simplifier =
    WriterT (Condition RewritingVariableName) simplifier

evaluateFunctions ::
    forall simplifier.
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    Map AxiomIdentifier [Equation RewritingVariableName] ->
    TermLike RewritingVariableName ->
    simplifier (Pattern RewritingVariableName)
evaluateFunctions sideCondition equations termLike = do
    (simplifiedTerm, newCondition) <- Writer.runWriterT (loop termLike)
    return (Pattern.withCondition simplifiedTerm newCondition)
  where
    loop ::
        TermLike RewritingVariableName ->
        FunctionEvaluator simplifier (TermLike RewritingVariableName)
    loop input = do
        output <- worker input
        if input == output
            then pure output
            else loop output

    worker ::
        TermLike RewritingVariableName ->
        FunctionEvaluator simplifier (TermLike RewritingVariableName)
    worker = Recursive.cata go

    go ::
        Recursive.Base
            (TermLike RewritingVariableName)
            (FunctionEvaluator simplifier (TermLike RewritingVariableName)) ->
        FunctionEvaluator simplifier (TermLike RewritingVariableName)
    go termLikeBase = do
        let attrs :< termLikeF = termLikeBase
        case termLikeF of
            TermLike.ApplySymbolF applySymbol -> do
                let TermLike.Application
                        { applicationChildren
                        } = applySymbol
                childrenResults <- sequence applicationChildren
                let appWithSimplifiedChildren =
                        applySymbol{TermLike.applicationChildren = childrenResults}
                    newAppTerm =
                        attrs :< TermLike.ApplySymbolF appWithSimplifiedChildren
                            & Recursive.embed
                result <-
                    evaluateFunction sideCondition equations newAppTerm
                        & runMaybeT
                        & lift
                case result of
                    Just simplifiedApp -> do
                        Writer.tell (Pattern.withoutTerm simplifiedApp)
                        return (extract simplifiedApp)
                    Nothing -> return newAppTerm
            _ -> Recursive.embed <$> sequence termLikeBase

-- TODO: we're already checking if this is an application pattern,
-- matchAxiomIdentifier is overkill
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

-- TODO: we're not actually doing anything with the errors here,
-- so I should simplify this
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
