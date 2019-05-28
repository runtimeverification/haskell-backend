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

import           Control.Error
                 ( atZ )
import           Control.Monad
                 ( when )
import           Control.Monad.Trans.Except
                 ( ExceptT (ExceptT) )
import qualified Data.Foldable as Foldable
import           Data.Function
import           Data.Maybe
                 ( isJust )
import qualified Data.Text as Text
import qualified Data.Text.Prettyprint.Doc as Pretty

import           Kore.Attribute.Symbol
                 ( Hook (..), StepperAttributes )
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SmtMetadataTools )
import qualified Kore.Internal.MultiOr as MultiOr
                 ( extractPatterns )
import qualified Kore.Internal.OrPattern as OrPattern
import           Kore.Internal.Pattern
                 ( Pattern )
import qualified Kore.Internal.Pattern as Pattern
import           Kore.Internal.TermLike
import           Kore.Step.Axiom.Data
                 ( AttemptedAxiom,
                 AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifier (..), BuiltinAndAxiomSimplifierMap )
import qualified Kore.Step.Axiom.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import qualified Kore.Step.Axiom.Data as AttemptedAxiom
                 ( AttemptedAxiom (..), exceptNotApplicable, hasRemainders )
import           Kore.Step.Axiom.Matcher
                 ( unificationWithAppMatchOnTop )
import qualified Kore.Step.Result as Result
import           Kore.Step.Rule
                 ( EqualityRule (EqualityRule) )
import qualified Kore.Step.Rule as RulePattern
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, Simplifier, TermLikeSimplifier )
import           Kore.Step.Step
                 ( UnificationProcedure (UnificationProcedure) )
import qualified Kore.Step.Step as Step
import qualified Kore.Unification.Unify as Monad.Unify
import           Kore.Unparser
                 ( Unparse, unparse )
import           Kore.Variables.Fresh
                 ( FreshVariable )

import qualified Kore.Proof.Value as Value

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
        ::  forall variable
        .   ( FreshVariable variable
            , Ord variable
            , SortedVariable variable
            , Show variable
            , Unparse variable
            )
        => SmtMetadataTools StepperAttributes
        -> PredicateSimplifier
        -> TermLikeSimplifier
        -> BuiltinAndAxiomSimplifierMap
        -> TermLike variable
        -> Simplifier (AttemptedAxiom variable)
    totalDefinitionEvaluationWorker
        tools
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
                tools
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
    :: forall variable
    .   ( FreshVariable variable
        , Ord variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        )
    => BuiltinAndAxiomSimplifier
    -> SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> Simplifier (AttemptedAxiom variable)
evaluateBuiltin
    (BuiltinAndAxiomSimplifier builtinEvaluator)
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    patt
  = do
    result <-
        builtinEvaluator
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            patt
    case result of
        AttemptedAxiom.NotApplicable
          | isPattConcrete
          , App_ appHead children <- patt
          , Just hook <- getAppHookString appHead
          , all isValue children ->
            error
                (   "Expecting hook " ++ hook
               ++  " to reduce concrete pattern\n\t"
                ++ show patt
                )
          | otherwise ->
            return AttemptedAxiom.NotApplicable
        AttemptedAxiom.Applied _ -> return result
  where
    isPattConcrete = isConcrete patt
    isValue pat = isJust $
        Value.fromConcreteStepPattern tools =<< asConcrete pat
    -- TODO(virgil): Send this from outside.
    getAppHookString appHead =
        Text.unpack <$> (getHook . Attribute.hook . symAttributes tools) appHead

applyFirstSimplifierThatWorks
    :: forall variable
    .   ( FreshVariable variable
        , Ord variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        )
    => [BuiltinAndAxiomSimplifier]
    -> AcceptsMultipleResults
    -> SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> Simplifier
        (AttemptedAxiom variable)
applyFirstSimplifierThatWorks [] _ _ _ _ _ _ =
    return AttemptedAxiom.NotApplicable
applyFirstSimplifierThatWorks
    (BuiltinAndAxiomSimplifier evaluator : evaluators)
    multipleResults
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    patt
  = do
    applicationResult <-
        evaluator
            tools substitutionSimplifier simplifier axiomIdToSimplifier patt

    case applicationResult of
        AttemptedAxiom.Applied AttemptedAxiomResults
            { results = orResults
            , remainders = orRemainders
            } -> do
                when
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
                when
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
                tools
                substitutionSimplifier
                simplifier
                axiomIdToSimplifier
                patt

evaluateWithDefinitionAxioms
    :: forall variable
    .   ( FreshVariable variable
        , Ord variable
        , SortedVariable variable
        , Show variable
        , Unparse variable
        )
    => [EqualityRule Variable]
    -> SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> TermLike variable
    -> Simplifier (AttemptedAxiom variable)
evaluateWithDefinitionAxioms
    definitionRules
    tools
    substitutionSimplifier
    simplifier
    axiomIdToSimplifier
    patt
  | invalidCoinduction = return AttemptedAxiom.NotApplicable
  | otherwise =
    AttemptedAxiom.exceptNotApplicable $ do
    let
        -- TODO (thomas.tuegel): Figure out how to get the initial conditions
        -- and apply them here, to remove remainder branches sooner.
        expanded :: Pattern variable
        expanded = Pattern.fromTermLike patt

    let unwrapEqualityRule =
            \(EqualityRule rule) ->
                RulePattern.mapVariables fromVariable rule
    results <- ExceptT $ Monad.Unify.runUnifier
        $ Step.sequenceRules
            tools
            substitutionSimplifier
            simplifier
            axiomIdToSimplifier
            (UnificationProcedure unificationWithAppMatchOnTop)
            expanded
            (map unwrapEqualityRule definitionRules)

    let
        result =
            Result.mergeResults results
            & Result.mapConfigs
                keepResultUnchanged
                markRemainderEvaluated
        keepResultUnchanged = id
        markRemainderEvaluated = fmap mkEvaluated

    return $ AttemptedAxiom.Applied AttemptedAxiomResults
        { results = Step.gatherResults result
        , remainders = Step.remainders result
        }

  where
    -- If the pattern is an application of a inductively-defined symbol,
    -- applying the definition axioms will not terminate, so we consider this
    -- case invalid.
    invalidCoinduction
      | App_ symbol children <- patt =
        let
            Attribute.Inductive { inductiveArguments } =
                Attribute.inductive (symAttributes tools symbol)
            hasInvalidArgument ix =
                maybe False (not . isConstructorPattern) (atZ children (ix - 1))
        in
            Foldable.any hasInvalidArgument inductiveArguments
      | otherwise = False

    isConstructorPattern termLike
      | App_ symbol _ <- termLike =
            symAttributes tools symbol
            & Attribute.constructor
            & Attribute.isConstructor
      | otherwise = False
