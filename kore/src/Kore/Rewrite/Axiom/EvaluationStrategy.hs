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
    simplificationEvaluation,
) where

import Data.Text qualified as Text
import Kore.Attribute.Symbol qualified as Attribute
import Kore.Equation qualified as Equation
import Kore.Equation.DebugEquation qualified as Equation
import Kore.Equation.Equation (
    Equation,
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
import Prelude.Kore
import Pretty (
    Pretty (..),
 )
import Pretty qualified

-- | Create an evaluator from a single simplification rule.
simplificationEvaluation ::
    Equation RewritingVariableName ->
    TermLike RewritingVariableName ->
    SideCondition RewritingVariableName ->
    Simplifier (AttemptedAxiom RewritingVariableName)
simplificationEvaluation equation term condition = do
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

{- | Wraps an evaluator for builtins. Will fail with error if there is no result
on concrete patterns.
-}
builtinEvaluation ::
    -- | Map from axiom IDs to axiom evaluators
    Simplifier (AttemptedAxiom RewritingVariableName) ->
    TermLike RewritingVariableName ->
    Simplifier (AttemptedAxiom RewritingVariableName)
builtinEvaluation builtinEvaluator patt =
    do
        result <- builtinEvaluator
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
