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
import Kore.Debug
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
    ( EqualityRule (..)
    , RulePattern (left)
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
import Kore.Unparser
import Kore.Variables.Fresh

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
        (\_ _ _ term predicate ->
            evaluateWithCheck rules term predicate
        )

-- | Create an evaluator from a single simplification rule.
simplificationEvaluation
    :: EqualityRule Variable
    -> BuiltinAndAxiomSimplifier
simplificationEvaluation rule =
    BuiltinAndAxiomSimplifier
        (\_ _ _ term predicate ->
            evaluateWithCheck [rule] term predicate
        )

evaluateWithCheck
    :: (Debug variable
      , FreshVariable variable
      , SortedVariable variable
      , Show variable
      , Unparse variable
      , MonadSimplify simplifier)
    => [EqualityRule Variable]
    -> TermLike variable
    -> Predicate variable
    -> simplifier (AttemptedAxiom variable)
evaluateWithCheck rules term predicate
  | not $ isFunctionPattern $ term
    = error "term is not function-like"
  | not $ all isFunctionPattern $ fmap (left . getEqualityRule) rules
    = error "rule is not function-like"
  | otherwise
    = evaluateAxioms rules term (Predicate.toPredicate predicate)

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
        => PredicateSimplifier
        -> TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> TermLike variable
        -> Predicate variable
        -> simplifier (AttemptedAxiom variable)
    totalDefinitionEvaluationWorker _ _ _ term predicate = do
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
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> Predicate variable
    -> simplifier (AttemptedAxiom variable)
evaluateBuiltin
    (BuiltinAndAxiomSimplifier builtinEvaluator)
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    patt
    predicate
  = do
    result <-
        builtinEvaluator
            substitutionSimplifier
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
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> Predicate variable
    -> simplifier (AttemptedAxiom variable)
applyFirstSimplifierThatWorks [] _ _ _ _ _ _ =
    return AttemptedAxiom.NotApplicable
applyFirstSimplifierThatWorks
    (BuiltinAndAxiomSimplifier evaluator : evaluators)
    multipleResults
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    patt
    predicate
  = do
    applicationResult <-
        evaluator
            substitutionSimplifier
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
              error
                  (  "Unexpected simplification result with more "
                  ++ "than one configuration: "
                  ++ show applicationResult
                  )
          | not (OrPattern.isFalse orRemainders) ->  do
              Logger.logDebug
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
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            patt
            predicate
