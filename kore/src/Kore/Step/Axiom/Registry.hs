{- |
Copyright   : (c) Runtime Verification, 2018
License     : BSD-3-Clause
-}
module Kore.Step.Axiom.Registry (
    mkEvaluatorRegistry,
    extractEquations,
) where

import Data.Map.Strict (
    Map,
 )
import Kore.Equation (
    Equation (..),
 )
import Prelude.Kore

-- TODO (thomas.tuegel): Remove private import
import Kore.Equation.Registry
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Step.Axiom.EvaluationStrategy (
    definitionEvaluation,
    firstFullEvaluation,
    simplificationEvaluation,
    simplifierWithFallback,
 )
import Kore.Step.Axiom.Identifier (
    AxiomIdentifier,
 )
import Kore.Step.Simplification.Simplify (
    BuiltinAndAxiomSimplifier (..),
 )

{- | Converts a collection of processed 'EqualityRule's to one of
 'BuiltinAndAxiomSimplifier's
-}
mkEvaluator ::
    PartitionedEquations ->
    Maybe BuiltinAndAxiomSimplifier
mkEvaluator PartitionedEquations{functionRules, simplificationRules} =
    case (simplificationEvaluator, definitionEvaluator) of
        (Nothing, Nothing) -> Nothing
        (Just evaluator, Nothing) -> Just evaluator
        (Nothing, Just evaluator) -> Just evaluator
        (Just sEvaluator, Just dEvaluator) ->
            Just (simplifierWithFallback dEvaluator sEvaluator)
  where
    simplificationEvaluator =
        if null simplificationRules
            then Nothing
            else
                Just . firstFullEvaluation $
                    simplificationEvaluation
                        <$> simplificationRules
    definitionEvaluator =
        if null functionRules
            then Nothing
            else Just $ definitionEvaluation functionRules

mkEvaluatorRegistry ::
    Map AxiomIdentifier [Equation RewritingVariableName] ->
    Map AxiomIdentifier BuiltinAndAxiomSimplifier
mkEvaluatorRegistry =
    mapMaybe (mkEvaluator . partitionEquations)
