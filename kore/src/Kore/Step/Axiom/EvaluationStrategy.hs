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
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Kore.Attribute.Symbol as Attribute
import qualified Kore.Internal.MultiOr as MultiOr
    ( extractPatterns
    )
import qualified Kore.Internal.OrPattern as OrPattern
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Internal.Symbol
import Kore.Internal.TermLike as TermLike
import Kore.Logger.WarnBottomHook
    ( warnBottomHook
    )
import Kore.Logger.WarnSimplificationWithRemainder
    ( warnSimplificationWithRemainder
    )
import Kore.Step.Axiom.Evaluate
import Kore.Step.EqualityPattern
    ( EqualityRule (..)
    )
import qualified Kore.Step.EquationalStep as Step
import Kore.Step.Result as Results
import Kore.Step.Simplification.Simplify
import qualified Kore.Step.Simplification.Simplify as AttemptedAxiom
    ( AttemptedAxiom (..)
    )
import qualified Kore.Step.Simplification.Simplify as AttemptedAxiomResults
    ( AttemptedAxiomResults (..)
    )
import Kore.TopBottom
    ( isBottom
    )
import Kore.Unparser
    ( unparse
    )

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
    BuiltinAndAxiomSimplifier $ \term condition -> do
        results' <- evaluateAxioms rules condition term
        let attempted = Results.toAttemptedAxiom results'
        Step.assertFunctionLikeResults term results'
        return attempted

-- | Create an evaluator from a single simplification rule.
simplificationEvaluation
    :: EqualityRule Variable
    -> BuiltinAndAxiomSimplifier
simplificationEvaluation rule =
    BuiltinAndAxiomSimplifier $ \term condition -> do
        results <- evaluateAxioms [rule] condition term
        let initial = Step.toConfigurationVariables (Pattern.fromTermLike term)
        Step.recoveryFunctionLikeResults initial results
        return $ Results.toAttemptedAxiom results

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
        .  ( SimplifierVariable variable
           , MonadSimplify simplifier
           )
        => TermLike variable
        -> SideCondition variable
        -> simplifier (AttemptedAxiom variable)
    totalDefinitionEvaluationWorker term sideCondition = do
        results <- evaluateAxioms rules sideCondition term
        let attempted = rejectRemainders $ Results.toAttemptedAxiom results
        Step.assertFunctionLikeResults term results
        return attempted

    rejectRemainders attempted
      | hasRemainders attempted = AttemptedAxiom.NotApplicable
      | otherwise               = attempted

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
    .  ( SimplifierVariable variable
       , MonadSimplify simplifier
       )
    => BuiltinAndAxiomSimplifier
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> SideCondition variable
    -> simplifier (AttemptedAxiom variable)
evaluateBuiltin
    (BuiltinAndAxiomSimplifier builtinEvaluator)
    patt
    sideCondition
  = do
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
        Applied AttemptedAxiomResults { results , remainders }
          | App_ appHead _ <- patt
          , Just hook_ <- Attribute.getHook (symbolHook appHead)
          , isBottom results
          , isBottom remainders -> do
              warnBottomHook hook_ patt
              return result
        _ -> return result
  where
    isValue pat =
        maybe False TermLike.isConstructorLike $ asConcrete pat

applyFirstSimplifierThatWorks
    :: forall variable simplifier
    .  ( SimplifierVariable variable
       , MonadSimplify simplifier
       )
    => [BuiltinAndAxiomSimplifier]
    -> AcceptsMultipleResults
    -> TermLike variable
    -> SideCondition variable
    -> simplifier (AttemptedAxiom variable)
applyFirstSimplifierThatWorks [] _ _ _ =
    return AttemptedAxiom.NotApplicable
applyFirstSimplifierThatWorks
    (BuiltinAndAxiomSimplifier evaluator : evaluators)
    multipleResults
    patt
    sideCondition
  = do
    applicationResult <- evaluator patt sideCondition

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
            warnSimplificationWithRemainder
                patt
                sideCondition
                orResults
                orRemainders
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
            patt
            sideCondition
