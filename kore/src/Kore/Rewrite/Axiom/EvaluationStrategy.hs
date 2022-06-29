{- |
Module      : Kore.Rewrite.Axiom.EvaluationStrategy
Description : Various strategies for axiom/builtin-based simplification.
Copyright   : (c) Runtime Verification, 2019-2021
License     : BSD-3-Clause
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Rewrite.Axiom.EvaluationStrategy (
    builtinEvaluation,
    definitionEvaluation,
    simplificationEvaluation,
    firstFullEvaluation,
    simplifierWithFallback,

    -- * For testing
    attemptEquationAndAccumulateErrors,
    attemptEquations,
) where

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
import Data.Text qualified as Text
import Kore.Attribute.Symbol qualified as Attribute
import Kore.Equation qualified as Equation
import Kore.Equation.DebugEquation (
    AttemptEquationError,
 )
import Kore.Equation.DebugEquation qualified as Equation
import Kore.Equation.Equation (
    Equation,
 )
import Kore.Internal.OrPattern (
    OrPattern,
 )
import Kore.Internal.OrPattern qualified as OrPattern
import Kore.Internal.SideCondition (
    SideCondition,
 )
import Kore.Internal.SideCondition qualified as SideCondition
import Kore.Internal.Symbol
import Kore.Internal.TermLike as TermLike
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify
import Kore.Simplify.Simplify qualified as AttemptedAxiom (
    AttemptedAxiom (..),
 )
import Kore.Unparser (
    unparse,
 )
import Kore.Variables.Target (
    Target,
 )
import Kore.Variables.Target qualified as Target
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import Pretty qualified

{- | Creates an evaluator for a function from the full set of rules
that define it.
-}
definitionEvaluation ::
    [Equation RewritingVariableName] ->
    BuiltinAndAxiomSimplifier
definitionEvaluation equations =
    BuiltinAndAxiomSimplifier $ \term condition -> do
        let term' = TermLike.mapVariables Target.mkUnifiedNonTarget term
        result <-
            attemptEquations
                (attemptEquationAndAccumulateErrors condition term')
                equations
        case result of
            Right results ->
                (return . Applied)
                    AttemptedAxiomResults
                        { results
                        , remainders = OrPattern.bottom
                        }
            Left minError ->
                case getMin <$> getOption minError of
                    Just (Equation.WhileCheckRequires _) ->
                        (return . NotApplicableUntilConditionChanges)
                            (SideCondition.toRepresentation condition)
                    _ -> return NotApplicable

attemptEquationAndAccumulateErrors ::
    MonadSimplify simplifier =>
    SideCondition RewritingVariableName ->
    TermLike (Target RewritingVariableName) ->
    Equation RewritingVariableName ->
    ExceptRT
        (OrPattern RewritingVariableName)
        simplifier
        (Option (Min (AttemptEquationError RewritingVariableName)))
attemptEquationAndAccumulateErrors condition term equation =
    attemptEquation
  where
    attemptEquation =
        ExceptRT . ExceptT $
            Equation.attemptEquation
                condition
                (TermLike.mapVariables (pure Target.unTarget) term)
                equation
                >>= either (return . Left . Option . Just . Min) (fmap Right . apply)
    apply = Equation.applyEquation condition equation

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

-- | Create an evaluator from a single simplification rule.
simplificationEvaluation ::
    Equation RewritingVariableName ->
    BuiltinAndAxiomSimplifier
simplificationEvaluation equation =
    BuiltinAndAxiomSimplifier $ \term condition -> do
        result <-
            Equation.attemptEquation
                condition
                term
                equation
        let apply = Equation.applyEquation condition equation
        case result of
            Right applied -> do
                results <- apply applied
                (return . Applied)
                    AttemptedAxiomResults
                        { results
                        , remainders = OrPattern.bottom
                        }
            Left err ->
                case err of
                    Equation.WhileCheckRequires _ ->
                        (return . NotApplicableUntilConditionChanges)
                            (SideCondition.toRepresentation condition)
                    _ -> return NotApplicable

{- | Creates an evaluator that choses the result of the first evaluator if it
returns Applicable, otherwise returns the result of the second.
-}
simplifierWithFallback ::
    BuiltinAndAxiomSimplifier ->
    BuiltinAndAxiomSimplifier ->
    BuiltinAndAxiomSimplifier
simplifierWithFallback first second =
    BuiltinAndAxiomSimplifier
        (applyFirstSimplifierThatWorks [first, second] WithMultipleResults)

{- | Wraps an evaluator for builtins. Will fail with error if there is no result
on concrete patterns.
-}
builtinEvaluation ::
    BuiltinAndAxiomSimplifier ->
    BuiltinAndAxiomSimplifier
builtinEvaluation evaluator =
    BuiltinAndAxiomSimplifier (evaluateBuiltin evaluator)

evaluateBuiltin ::
    forall simplifier.
    MonadSimplify simplifier =>
    -- | Map from axiom IDs to axiom evaluators
    BuiltinAndAxiomSimplifier ->
    TermLike RewritingVariableName ->
    SideCondition RewritingVariableName ->
    simplifier (AttemptedAxiom RewritingVariableName)
evaluateBuiltin
    (BuiltinAndAxiomSimplifier builtinEvaluator)
    patt
    sideCondition =
        do
            result <- builtinEvaluator patt sideCondition
            case result of
                AttemptedAxiom.NotApplicable
                    | App_ appHead children <- patt
                      , Just hook_ <- Text.unpack <$> Attribute.getHook (symbolHook appHead)
                      , all isValue children ->
                        (error . show . Pretty.vsep)
                            [ "Expecting hook "
                                <> Pretty.squotes (Pretty.pretty hook_)
                                <> " to reduce concrete pattern:"
                            , Pretty.indent 4 (unparse patt)
                            ]
                _ -> return result
      where
        isValue pat =
            maybe False TermLike.isConstructorLike $ asConcrete pat
