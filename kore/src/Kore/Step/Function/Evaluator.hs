{-|
Module      : Kore.Step.Function.Evaluator
Description : Evaluates functions in a pattern.
Copyright   : (c) Runtime Verification, 2018
License     : NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Function.Evaluator
    ( evaluateApplication
    , evaluatePattern
    ) where

import           Control.Exception
                 ( assert )
import qualified Data.Functor.Foldable as Recursive
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )
import           Data.Reflection
                 ( give )
import qualified Data.Text as Text

import qualified Kore.AST.Common as Common
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( Hook (..), StepperAttributes, isSortInjection_ )
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.Debug
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..), SmtMetadataTools )
import           Kore.Step.Axiom.Data
                 ( AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifier (..), BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Axiom.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import qualified Kore.Step.Axiom.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import           Kore.Step.Axiom.Identifier
                 ( AxiomIdentifier )
import qualified Kore.Step.Axiom.Identifier as AxiomIdentifier
                 ( extract )
import qualified Kore.Step.Merging.OrPattern as OrPattern
import           Kore.Step.OrPattern
                 ( OrPattern )
import qualified Kore.Step.OrPattern as OrPattern
import           Kore.Step.Pattern
                 ( Conditional (..), Pattern, Predicate )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( flatten, merge, traverseWithPairs )
import           Kore.Step.Simplification.Data
                 ( PredicateSimplifier, SimplificationProof (..), Simplifier,
                 TermLikeSimplifier, simplifyTerm )
import qualified Kore.Step.Simplification.Pattern as Pattern
import           Kore.Step.TermLike
import           Kore.Syntax.Application
import           Kore.Syntax.Id
import           Kore.Unparser
import           Kore.Variables.Fresh

{-| Evaluates functions on an application pattern.
-}
evaluateApplication
    ::  forall variable.
        ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Predicate variable
    -- ^ Aggregated children predicate and substitution.
    -> CofreeF
        (Application SymbolOrAlias)
        (Valid variable Object)
        (TermLike variable)
    -- ^ The pattern to be evaluated
    -> Simplifier
        (OrPattern variable, SimplificationProof Object)
evaluateApplication
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    childrenPredicate
    (valid :< app)
  = case maybeEvaluatedPattSimplifier of
        Nothing
          | Just hook <- getAppHookString
          , not(null axiomIdToEvaluator) ->
            error
                (   "Attempting to evaluate unimplemented hooked operation "
                ++  hook ++ ".\nSymbol: " ++ getIdForError symbolId
                )
          | otherwise ->
            return unchanged
        Just evaluatedPattSimplifier -> evaluatedPattSimplifier
  where
    (afterInj, _proof) = evaluateSortInjection tools app

    maybeEvaluatedPattSimplifier =
        maybeEvaluatePattern
            tools
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            childrenPredicate
            appPurePattern
            unchangedOr

    Application { applicationSymbolOrAlias = appHead } = afterInj
    SymbolOrAlias { symbolOrAliasConstructor = symbolId } = appHead

    appPurePattern =
        Recursive.embed (valid :< Common.ApplicationPattern afterInj)

    unchangedPatt =
        Conditional
            { term         = appPurePattern
            , predicate    = predicate
            , substitution = substitution
            }
      where
        Conditional { term = (), predicate, substitution } =
            childrenPredicate
    unchangedOr = OrPattern.fromPattern unchangedPatt
    unchanged = (unchangedOr, SimplificationProof)

    getAppHookString =
        Text.unpack <$> (getHook . Attribute.hook . symAttributes tools) appHead

{-| Evaluates axioms on patterns.
-}
evaluatePattern
    ::  forall variable .
        ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Predicate variable
    -- ^ Aggregated children predicate and substitution.
    -> TermLike variable
    -- ^ The pattern to be evaluated
    -> OrPattern variable
    -- ^ The default value
    -> Simplifier
        (OrPattern variable, SimplificationProof Object)
evaluatePattern
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    childrenPredicate
    patt
    defaultValue
  =
    fromMaybe
        (return (defaultValue, SimplificationProof))
        (maybeEvaluatePattern
            tools
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            childrenPredicate
            patt
            defaultValue
        )

{-| Evaluates axioms on patterns.

Returns Nothing if there is no axiom for the pattern's identifier.
-}
maybeEvaluatePattern
    ::  forall variable .
        ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Predicate variable
    -- ^ Aggregated children predicate and substitution.
    -> TermLike variable
    -- ^ The pattern to be evaluated
    -> OrPattern variable
    -- ^ The default value
    -> Maybe
        (Simplifier
            (OrPattern variable, SimplificationProof Object)
        )
maybeEvaluatePattern
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    childrenPredicate
    patt
    defaultValue
  =
    case maybeEvaluator of
        Nothing -> Nothing
        Just (BuiltinAndAxiomSimplifier evaluator) ->
            Just
            $ traceNonErrorMonad
                D_Function_evaluatePattern
                [ debugArg "axiomIdentifier" identifier ]
            $ do
                (result, proof) <-
                    evaluator
                        tools
                        substitutionSimplifier
                        simplifier
                        axiomIdToEvaluator
                        patt
                flattened <- case result of
                    AttemptedAxiom.NotApplicable ->
                        return AttemptedAxiom.NotApplicable
                    AttemptedAxiom.Applied AttemptedAxiomResults
                        { results = orResults
                        , remainders = orRemainders
                        } -> do
                            simplified <- mapM simplifyIfNeeded orResults
                            return
                                (AttemptedAxiom.Applied AttemptedAxiomResults
                                    { results =
                                        MultiOr.flatten simplified
                                    , remainders = orRemainders
                                    }
                                )
                (merged, _proof) <- mergeWithConditionAndSubstitution
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToEvaluator
                    childrenPredicate
                    (flattened, proof)
                case merged of
                    AttemptedAxiom.NotApplicable ->
                        return (defaultValue, SimplificationProof)
                    AttemptedAxiom.Applied AttemptedAxiomResults
                        { results, remainders } ->
                            return
                                ( MultiOr.merge results remainders
                                , SimplificationProof
                                )
  where
    identifier :: Maybe (AxiomIdentifier Object)
    identifier = AxiomIdentifier.extract patt

    maybeEvaluator :: Maybe (BuiltinAndAxiomSimplifier Object)
    maybeEvaluator = do
        identifier' <- identifier
        Map.lookup identifier' axiomIdToEvaluator

    unchangedPatt =
        Conditional
            { term         = patt
            , predicate    = predicate
            , substitution = substitution
            }
      where
        Conditional { term = (), predicate, substitution } =
            childrenPredicate

    simplifyIfNeeded
        :: Pattern variable
        -> Simplifier (OrPattern variable)
    simplifyIfNeeded toSimplify =
        if toSimplify == unchangedPatt
            then return (OrPattern.fromPattern unchangedPatt)
            else
                reevaluateFunctions
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToEvaluator
                    toSimplify

evaluateSortInjection
    :: Ord variable
    => SmtMetadataTools StepperAttributes
    -> Application SymbolOrAlias (TermLike variable)
    ->  ( Application SymbolOrAlias (TermLike variable)
        , SimplificationProof Object
        )
evaluateSortInjection tools ap
  | give tools isSortInjection_ apHead
  = case apChild of
    (App_ apHeadChild grandChildren)
      | give tools isSortInjection_ apHeadChild ->
        let
            [fromSort', toSort'] = symbolOrAliasParams apHeadChild
            apHeadNew = updateSortInjectionSource apHead fromSort'
            resultApp = apHeadNew grandChildren
        in
            assert (toSort' == fromSort) $
                ( resultApp
                , SimplificationProof
                )
    _ -> (ap, SimplificationProof)
  | otherwise = (ap, SimplificationProof)
  where
    apHead = applicationSymbolOrAlias ap
    [fromSort, _] = symbolOrAliasParams apHead
    [apChild] = applicationChildren ap
    updateSortInjectionSource head1 fromSort1 =
        \children ->
            ( Application
                { applicationSymbolOrAlias =
                    head1 { symbolOrAliasParams = [fromSort1, toSort1] }
                , applicationChildren = children
                }
            )
      where
        [_, toSort1] = symbolOrAliasParams head1

{-| 'reevaluateFunctions' re-evaluates functions after a user-defined function
was evaluated.
-}
reevaluateFunctions
    ::  ( SortedVariable variable
        , Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions in patterns.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Pattern variable
    -- ^ Function evaluation result.
    -> Simplifier (OrPattern variable)
reevaluateFunctions
    tools
    substitutionSimplifier
    termSimplifier
    axiomIdToEvaluator
    Conditional
        { term   = rewrittenPattern
        , predicate = rewritingCondition
        , substitution = rewrittenSubstitution
        }
  = do
    (pattOr , _proof) <- simplifyTerm' rewrittenPattern
    (mergedPatt, _proof) <-
        OrPattern.mergeWithPredicate
            tools
            substitutionSimplifier
            termSimplifier
            axiomIdToEvaluator
            Conditional
                { term = ()
                , predicate = rewritingCondition
                , substitution = rewrittenSubstitution
                }
            pattOr
    (evaluatedPatt, _) <-
        MultiOr.traverseWithPairs
            (Pattern.simplifyPredicate
                tools
                substitutionSimplifier
                termSimplifier
                axiomIdToEvaluator
            )
            mergedPatt
    return evaluatedPatt
  where
    simplifyTerm' = simplifyTerm termSimplifier substitutionSimplifier

{-| Ands the given condition-substitution to the given function evaluation.
-}
mergeWithConditionAndSubstitution
    ::  ( Ord variable
        , Show variable
        , Unparse variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => SmtMetadataTools StepperAttributes
    -> PredicateSimplifier
    -> TermLikeSimplifier
    -- ^ Evaluates functions in a pattern.
    -> BuiltinAndAxiomSimplifierMap
    -- ^ Map from axiom IDs to axiom evaluators
    -> Predicate variable
    -- ^ Condition and substitution to add.
    -> (AttemptedAxiom Object variable, SimplificationProof Object)
    -- ^ AttemptedAxiom to which the condition should be added.
    -> Simplifier (AttemptedAxiom Object variable, SimplificationProof Object)
mergeWithConditionAndSubstitution
    _ _ _ _ _ (AttemptedAxiom.NotApplicable, _proof)
  =
    return (AttemptedAxiom.NotApplicable, SimplificationProof)
mergeWithConditionAndSubstitution
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    toMerge
    ( AttemptedAxiom.Applied AttemptedAxiomResults { results, remainders }
    , _proof
    )
  = do
    (evaluatedResults, _proof) <-
        OrPattern.mergeWithPredicate
            tools
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            toMerge
            results
    (evaluatedRemainders, _proof) <-
        OrPattern.mergeWithPredicate
            tools
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            toMerge
            remainders
    return
        ( AttemptedAxiom.Applied AttemptedAxiomResults
            { results = evaluatedResults, remainders = evaluatedRemainders }
        , SimplificationProof
        )
