{-|
Module      : Kore.Step.Function.EvaluationStrategy
Description : Various strategies for evaluating functions.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Function.EvaluationStrategy
    ( builtinEvaluation
    , definitionEvaluation
    , firstFullEvaluation
    , simplifierWithFallback
    ) where

import Kore.Step.AxiomPatterns
       ( EqualityRule )
import Kore.Step.Function.Data
       ( BuiltinAndAxiomSimplifier (..) )
import Kore.Step.Function.Evaluator
       ( AcceptsMultipleResults (..), applyFirstSimplifierThatWorks,
       evaluateBuiltin, evaluateWithDefinitionAxioms )

{-| Creates an evaluator for a function from the full set of rules
that define it.
-}
definitionEvaluation
    :: [EqualityRule level]
    -> BuiltinAndAxiomSimplifier level
definitionEvaluation rules =
    BuiltinAndAxiomSimplifier
        (evaluateWithDefinitionAxioms rules)

{-| Creates an evaluator that choses the result of the first evaluator that
returns Applicable.

If that result contains more than one pattern, or it contains a reminder,
the evaluation fails with 'error' (may change in the future).
-}
firstFullEvaluation
    :: [BuiltinAndAxiomSimplifier level]
    -> BuiltinAndAxiomSimplifier level
firstFullEvaluation simplifiers =
    BuiltinAndAxiomSimplifier
        (applyFirstSimplifierThatWorks simplifiers OnlyOneResult)

{-| Creates an evaluator that choses the result of the first evaluator if it
returns Applicable, otherwise returns the result of the second.
-}
simplifierWithFallback
    :: BuiltinAndAxiomSimplifier level
    -> BuiltinAndAxiomSimplifier level
    -> BuiltinAndAxiomSimplifier level
simplifierWithFallback first second =
    BuiltinAndAxiomSimplifier
        (applyFirstSimplifierThatWorks [first, second] WithMultipleResults)

{-| Wraps an evaluator for builtins. Will fail with error if there is no result
on concrete patterns.
-}
builtinEvaluation
    :: BuiltinAndAxiomSimplifier level
    -> BuiltinAndAxiomSimplifier level
builtinEvaluation evaluator =
    BuiltinAndAxiomSimplifier (evaluateBuiltin evaluator)

