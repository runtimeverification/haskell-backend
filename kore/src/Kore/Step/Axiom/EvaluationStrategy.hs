{-|
Module      : Kore.Step.Axiom.EvaluationStrategy
Description : Various strategies for axiom/builtin-based simplification.
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Axiom.EvaluationStrategy
    ( builtinEvaluation
    , definitionEvaluation
    , simplificationEvaluation
    , totalDefinitionEvaluation
    , firstFullEvaluation
    , simplifierWithFallback
    ) where

import qualified Data.Foldable as Foldable
import Data.Maybe
    ( isJust
    )
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty
import qualified Data.Text.Prettyprint.Doc.Render.Text as Pretty

import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Internal.MultiOr as MultiOr
    ( extractPatterns
    )
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Predicate
    ( Predicate
    )
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.Symbol
import Kore.Internal.TermLike
import qualified Kore.Proof.Value as Value
import Kore.Step.Axiom.Evaluate
import Kore.Step.Rule
    ( EqualityRule
    )
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.Simplify as AttemptedAxiom
    ( AttemptedAxiom (..)
    , hasRemainders
    )
import qualified Kore.Step.Simplification.Simplify as AttemptedAxiomResults
    ( AttemptedAxiomResults (..)
    )
import Kore.Unparser
    ( unparse
    )

import qualified Kore.Logger as Logger

{-|Describes whether simplifiers are allowed to return multiple results or not.
-}
data AcceptsMultipleResults = WithMultipleResults | OnlyOneResult
    deriving (Eq, Ord, Show)

{-|Converts 'AcceptsMultipleResults' to Bool.
-}
acceptsMultipleResults :: AcceptsMultipleResults -> Bool
acceptsMultipleResults WithMultipleResults = True
acceptsMultipleResults OnlyOneResult = False

{-| Creates an evaluator for a function from the full set of rules
that define it.
-}
definitionEvaluation
    :: [EqualityRule Variable]
    -> BuiltinAndAxiomSimplifier
definitionEvaluation rules =
    BuiltinAndAxiomSimplifier
        (\_ _ term predicate ->
            evaluateAxioms rules term (Predicate.toPredicate predicate)
        )

-- | Create an evaluator from a single simplification rule.
simplificationEvaluation
    :: EqualityRule Variable
    -> BuiltinAndAxiomSimplifier
simplificationEvaluation rule =
    BuiltinAndAxiomSimplifier
        (\_ _ term predicate ->
            evaluateAxioms [rule] term (Predicate.toPredicate predicate)
        )

{- | Creates an evaluator for a function from all the rules that define it.

The function is not applied (@totalDefinitionEvaluation@ returns
'AttemptedAxiom.NotApplicable') if the supplied rules do not match the entire
input.

See also: 'definitionEvaluation'

-}
totalDefinitionEvaluation
    :: [EqualityRule Variable]
    -> BuiltinAndAxiomSimplifier
totalDefinitionEvaluation rules =
    BuiltinAndAxiomSimplifier totalDefinitionEvaluationWorker
  where
    totalDefinitionEvaluationWorker
        :: forall variable simplifier
        .  (SimplifierVariable variable, MonadSimplify simplifier)
        => TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> TermLike variable
        -> Predicate variable
        -> simplifier (AttemptedAxiom variable)
    totalDefinitionEvaluationWorker _ _ term predicate = do
        result <- evaluateAxioms rules term (Predicate.toPredicate predicate)
        if AttemptedAxiom.hasRemainders result
            then return AttemptedAxiom.NotApplicable
            else return result

{-| Creates an evaluator that choses the result of the first evaluator that
returns Applicable.

If that result contains more than one pattern, or it contains a reminder,
the evaluation fails with 'error' (may change in the future).
-}
firstFullEvaluation
    :: [BuiltinAndAxiomSimplifier]
    -> BuiltinAndAxiomSimplifier
firstFullEvaluation simplifiers =
    BuiltinAndAxiomSimplifier
        (applyFirstSimplifierThatWorks simplifiers OnlyOneResult)

{-| Creates an evaluator that choses the result of the first evaluator if it
returns Applicable, otherwise returns the result of the second.
-}
simplifierWithFallback
    :: BuiltinAndAxiomSimplifier
    -> BuiltinAndAxiomSimplifier
    -> BuiltinAndAxiomSimplifier
simplifierWithFallback first second =
    BuiltinAndAxiomSimplifier
        (applyFirstSimplifierThatWorks [first, second] WithMultipleResults)

{-| Wraps an evaluator for builtins. Will fail with error if there is no result
on concrete patterns.
-}
builtinEvaluation
    :: BuiltinAndAxiomSimplifier
    -> BuiltinAndAxiomSimplifier
builtinEvaluation evaluator =
    BuiltinAndAxiomSimplifier (evaluateBuiltin evaluator)


evaluateBuiltin
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => BuiltinAndAxiomSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> Predicate variable
    -> simplifier (AttemptedAxiom variable)
evaluateBuiltin
    (BuiltinAndAxiomSimplifier builtinEvaluator)
    simplifier
    axiomIdToSimplifier
    patt
    predicate
  = do
    result <-
        builtinEvaluator
            simplifier
            axiomIdToSimplifier
            patt
            predicate
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
    isValue pat = isJust $ Value.fromTermLike =<< asConcrete pat

applyFirstSimplifierThatWorks
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => [BuiltinAndAxiomSimplifier]
    -> AcceptsMultipleResults
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> Predicate variable
    -> simplifier (AttemptedAxiom variable)
applyFirstSimplifierThatWorks [] _ _ _ _ _ =
    return AttemptedAxiom.NotApplicable
applyFirstSimplifierThatWorks
    (BuiltinAndAxiomSimplifier evaluator : evaluators)
    multipleResults
    simplifier
    axiomIdToSimplifier
    patt
    predicate
  = do
    applicationResult <-
        evaluator
            simplifier
            axiomIdToSimplifier
            patt
            predicate

    case applicationResult of
        AttemptedAxiom.Applied AttemptedAxiomResults
            { results = orResults
            , remainders = orRemainders
            }
          | acceptsMultipleResults multipleResults -> return applicationResult
          -- below this point multiple results are not accepted
          | length (MultiOr.extractPatterns orResults) > 1 ->
              -- We should only allow multiple simplification results
              -- when they are created by unification splitting the
              -- configuration.
              -- However, right now, we shouldn't be able to get more
              -- than one result, so we throw an error.
              error . show . Pretty.vsep $
                [ "Unexpected simplification result with more \
                  \than one configuration:"
                , Pretty.indent 2 "input:"
                , Pretty.indent 4 (unparse patt)
                , Pretty.indent 2 "results:"
                , (Pretty.indent 4 . Pretty.vsep)
                    (unparse <$> Foldable.toList orResults)
                , Pretty.indent 2 "remainders:"
                , (Pretty.indent 4 . Pretty.vsep)
                    (unparse <$> Foldable.toList orRemainders)
                ]
          | not (OrPattern.isFalse orRemainders) ->  do
              Logger.logWarning
                  . Pretty.renderStrict . Pretty.layoutCompact . Pretty.vsep
                  $ [ "Simplification result with remainder:"
                    , Pretty.indent 2 "input:"
                    , Pretty.indent 4 (unparse patt)
                    , Pretty.indent 2 "results:"
                    , (Pretty.indent 4 . Pretty.vsep)
                        (unparse <$> Foldable.toList orResults)
                    , Pretty.indent 2 "remainders:"
                    , (Pretty.indent 4 . Pretty.vsep)
                        (unparse <$> Foldable.toList orRemainders)
                    , "Rule will be skipped."
                    ]
              -- TODO (traiansf): this might generate too much output
              --    replace log with a logOnce when that becomes available
              tryNextSimplifier
          | otherwise -> return applicationResult
        AttemptedAxiom.NotApplicable -> tryNextSimplifier
  where
    tryNextSimplifier =
        applyFirstSimplifierThatWorks
            evaluators
            multipleResults
            simplifier
            axiomIdToSimplifier
            patt
            predicate
