{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
-}
module Kore.Rewrite.Axiom.Registry (
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
import Kore.Rewrite.Axiom.EvaluationStrategy (
    definitionEvaluation,
    firstFullEvaluation,
    simplificationEvaluation,
    simplifierWithFallback,
 )
import Kore.Rewrite.Axiom.Identifier (
    AxiomIdentifier,
 )
import Kore.Rewrite.RewritingVariable (
    RewritingVariableName,
 )
import Kore.Simplify.Simplify (
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
