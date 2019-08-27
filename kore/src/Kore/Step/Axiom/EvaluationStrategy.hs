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
    , totalDefinitionEvaluation
    , firstFullEvaluation
    , simplifierWithFallback
    ) where

import qualified Control.Monad as Monad
import qualified Control.Monad.Trans.Class as Monad.Trans
import qualified Data.Foldable as Foldable
import           Data.Function
import           Data.Maybe
                 ( isJust )
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty

import qualified Kore.Attribute.Axiom as Attribute.Axiom
import qualified Kore.Attribute.Axiom.Concrete as Axiom.Concrete
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.Internal.Conditional
                 ( andCondition )
import qualified Kore.Internal.MultiOr as MultiOr
                 ( extractPatterns )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.Symbol
import           Kore.Internal.TermLike
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Proof.Value as Value
import           Kore.Step.Axiom.Matcher
                 ( matchIncremental )
import           Kore.Step.Remainder
                 ( ceilChildOfApplicationOrTop )
import qualified Kore.Step.Result as Result
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule, getEqualityRule) )
import qualified Kore.Step.Rule as RulePattern
import           Kore.Step.Simplification.Data
                 ( AttemptedAxiom,
                 AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifier (..), BuiltinAndAxiomSimplifierMap,
                 MonadSimplify, PredicateSimplifier, TermLikeSimplifier )
import qualified Kore.Step.Simplification.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import qualified Kore.Step.Simplification.Data as AttemptedAxiom
                 ( AttemptedAxiom (..), hasRemainders, maybeNotApplicable )
import qualified Kore.Step.Simplification.OrPattern as OrPattern
                 ( simplifyPredicatesWithSmt )
import           Kore.Step.Step
                 ( UnificationProcedure (UnificationProcedure) )
import qualified Kore.Step.Step as Step
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
                 ( Unparse, unparse )
import           Kore.Variables.Fresh
                 ( FreshVariable )

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
        (evaluateWithDefinitionAxioms rules)

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
        ::  forall variable simplifier
        .   ( FreshVariable variable
            , SortedVariable variable
            , Show variable
            , Unparse variable
            , MonadSimplify simplifier
            )
        => PredicateSimplifier
        -> TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> TermLike variable
        -> simplifier (AttemptedAxiom variable)
    totalDefinitionEvaluationWorker
        predicateSimplifier
        termSimplifier
        axiomSimplifiers
        term
      = do
        result <- evaluate term
        if AttemptedAxiom.hasRemainders result
            then return AttemptedAxiom.NotApplicable
            else return result
      where
        evaluate =
            evaluateWithDefinitionAxioms
                rules
                predicateSimplifier
                termSimplifier
                axiomSimplifiers

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
    .   ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        )
    => BuiltinAndAxiomSimplifier
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> simplifier (AttemptedAxiom variable)
evaluateBuiltin
    (BuiltinAndAxiomSimplifier builtinEvaluator)
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    patt
  = do
    result <-
        builtinEvaluator
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            patt
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
    .   ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        )
    => [BuiltinAndAxiomSimplifier]
    -> AcceptsMultipleResults
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> simplifier (AttemptedAxiom variable)
applyFirstSimplifierThatWorks [] _ _ _ _ _ =
    return AttemptedAxiom.NotApplicable
applyFirstSimplifierThatWorks
    (BuiltinAndAxiomSimplifier evaluator : evaluators)
    multipleResults
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    patt
  = do
    applicationResult <-
        evaluator substitutionSimplifier simplifier axiomIdToSimplifier patt

    case applicationResult of
        AttemptedAxiom.Applied AttemptedAxiomResults
            { results = orResults
            , remainders = orRemainders
            } -> do
                Monad.when
                    (length (MultiOr.extractPatterns orResults) > 1
                    && not (acceptsMultipleResults multipleResults)
                    )
                    -- We should only allow multiple simplification results
                    -- when they are created by unification splitting the
                    -- configuration.
                    -- However, right now, we shouldn't be able to get more
                    -- than one result, so we throw an error.
                    (error
                        (  "Unexpected simplification result with more "
                        ++ "than one configuration: "
                        ++ show applicationResult
                        )
                    )
                Monad.when
                    (not (OrPattern.isFalse orRemainders)
                    && not (acceptsMultipleResults multipleResults)
                    )
                    -- It's not obvious that we should accept simplifications
                    -- that change only a part of the configuration, since
                    -- that will probably make things more complicated.
                    --
                    -- Until we have a clear example that this can actually
                    -- happen, we throw an error.
                    ((error . show . Pretty.vsep)
                        [ "Unexpected simplification result with remainder:"
                        , Pretty.indent 2 "input:"
                        , Pretty.indent 4 (unparse patt)
                        , Pretty.indent 2 "results:"
                        , (Pretty.indent 4 . Pretty.vsep)
                            (unparse <$> Foldable.toList orResults)
                        , Pretty.indent 2 "remainders:"
                        , (Pretty.indent 4 . Pretty.vsep)
                            (unparse <$> Foldable.toList orRemainders)
                        ]
                    )
                return applicationResult
        AttemptedAxiom.NotApplicable ->
            applyFirstSimplifierThatWorks
                evaluators
                multipleResults
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                patt

evaluateWithDefinitionAxioms
    :: forall variable simplifier
    .   ( FreshVariable variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        , MonadSimplify simplifier
        )
    => [EqualityRule Variable]
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> simplifier (AttemptedAxiom variable)
evaluateWithDefinitionAxioms
    definitionRules
    _predicateSimplifier
    _termSimplifier
    _axiomSimplifiers
    patt
  | any ruleIsConcrete definitionRules
  , not (TermLike.isConcrete patt)
  = return AttemptedAxiom.NotApplicable
  | otherwise
  = AttemptedAxiom.maybeNotApplicable $ do
    let
        -- TODO (thomas.tuegel): Figure out how to get the initial conditions
        -- and apply them here, to remove remainder branches sooner.
        expanded :: Pattern variable
        expanded = Pattern.fromTermLike patt

    results <- applyRules expanded (map unwrapEqualityRule definitionRules)
    Monad.guard (any Result.hasResults results)
    mapM_ rejectNarrowing results

    ceilChild <- ceilChildOfApplicationOrTop patt
    let
        result =
            Result.mergeResults results
            & Result.mapConfigs
                keepResultUnchanged
                ( markRemainderEvaluated
                . introduceDefinedness ceilChild
                )
        keepResultUnchanged = id
        introduceDefinedness = flip andCondition
        markRemainderEvaluated = fmap mkEvaluated

    simplifiedResults <-
        Monad.Trans.lift
        $ OrPattern.simplifyPredicatesWithSmt (Step.gatherResults result)
    simplifiedRemainders <-
        Monad.Trans.lift
        $ OrPattern.simplifyPredicatesWithSmt (Step.remainders result)

    return $ AttemptedAxiom.Applied AttemptedAxiomResults
        { results = simplifiedResults
        , remainders = simplifiedRemainders
        }

  where
    ruleIsConcrete =
        Axiom.Concrete.isConcrete
        . Attribute.Axiom.concrete
        . RulePattern.attributes
        . getEqualityRule

    unwrapEqualityRule (EqualityRule rule) =
        RulePattern.mapVariables fromVariable rule

    rejectNarrowing (Result.results -> results) =
        (Monad.guard . not) (Foldable.any Step.isNarrowingResult results)

    applyRules initial rules =
        Monad.Unify.maybeUnifierT
        $ Step.applyRulesSequence unificationProcedure initial rules

    ignoreUnificationErrors unification pattern1 pattern2 =
        Monad.Unify.runUnifierT (unification pattern1 pattern2)
        >>= either (couldNotMatch pattern1 pattern2) Monad.Unify.scatter

    couldNotMatch pattern1 pattern2 _ =
        Monad.Unify.explainAndReturnBottom
            "Could not match patterns"
            pattern1
            pattern2

    unificationProcedure =
        UnificationProcedure (ignoreUnificationErrors matchIncremental)
