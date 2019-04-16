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
import qualified Data.Map as Map
import           Data.Maybe
                 ( fromMaybe )
import           Data.Reflection
                 ( give )
import qualified Data.Text as Text

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Attribute.Symbol
                 ( Hook (..), StepperAttributes, isSortInjection_ )
import qualified Kore.Attribute.Symbol as Attribute
import           Kore.Debug
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
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
import qualified Kore.Step.Merging.OrOfExpandedPattern as OrOfExpandedPattern
                 ( mergeWithPredicateSubstitution )
import           Kore.Step.Pattern
import           Kore.Step.Representation.ExpandedPattern
                 ( ExpandedPattern, PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.Representation.MultiOr as MultiOr
                 ( flatten, make, merge, traverseWithPairs )
import           Kore.Step.Representation.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier, simplifyTerm )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import           Kore.Unparser
import           Kore.Variables.Fresh

{-| Evaluates functions on an application pattern.
-}
evaluateApplication
    ::  forall level variable.
        ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> PredicateSubstitution level variable
    -- ^ Aggregated children predicate and substitution.
    -> CofreeF
        (Application level)
        (Valid (variable level) level)
        (StepPattern level variable)
    -- ^ The pattern to be evaluated
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
evaluateApplication
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    childrenPredicateSubstitution
    (valid :< app)
  = case maybeEvaluatedPattSimplifier of
        Nothing
          | Just hook <- getAppHookString
          , not(null axiomIdToEvaluator) ->
            error
                (   "Attempting to evaluate unimplemented hooked operation "
                ++  hook ++ ".\nSymbol: " ++ show (getId symbolId)
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
            childrenPredicateSubstitution
            appPurePattern
            unchangedOr

    Application { applicationSymbolOrAlias = appHead } = afterInj
    SymbolOrAlias { symbolOrAliasConstructor = symbolId } = appHead

    appPurePattern = asPurePattern (valid :< ApplicationPattern afterInj)

    unchangedPatt =
        Predicated
            { term         = appPurePattern
            , predicate    = predicate
            , substitution = substitution
            }
      where
        Predicated { term = (), predicate, substitution } =
            childrenPredicateSubstitution
    unchangedOr = MultiOr.make [unchangedPatt]
    unchanged = (unchangedOr, SimplificationProof)

    getAppHookString =
        Text.unpack <$> (getHook . Attribute.hook . symAttributes tools) appHead

{-| Evaluates axioms on patterns.
-}
evaluatePattern
    ::  forall level variable .
        ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> PredicateSubstitution level variable
    -- ^ Aggregated children predicate and substitution.
    -> StepPattern level variable
    -- ^ The pattern to be evaluated
    -> OrOfExpandedPattern level variable
    -- ^ The default value
    -> Simplifier
        (OrOfExpandedPattern level variable, SimplificationProof level)
evaluatePattern
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    childrenPredicateSubstitution
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
            childrenPredicateSubstitution
            patt
            defaultValue
        )

{-| Evaluates axioms on patterns.

Returns Nothing if there is no axiom for the pattern's identifier.
-}
maybeEvaluatePattern
    ::  forall level variable .
        ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> PredicateSubstitution level variable
    -- ^ Aggregated children predicate and substitution.
    -> StepPattern level variable
    -- ^ The pattern to be evaluated
    -> OrOfExpandedPattern level variable
    -- ^ The default value
    -> Maybe
        (Simplifier
            (OrOfExpandedPattern level variable, SimplificationProof level)
        )
maybeEvaluatePattern
    tools
    substitutionSimplifier
    simplifier
    axiomIdToEvaluator
    childrenPredicateSubstitution
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
                    childrenPredicateSubstitution
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
    identifier :: Maybe (AxiomIdentifier level)
    identifier = AxiomIdentifier.extract patt

    maybeEvaluator :: Maybe (BuiltinAndAxiomSimplifier level)
    maybeEvaluator = do
        identifier' <- identifier
        Map.lookup identifier' axiomIdToEvaluator

    unchangedPatt =
        Predicated
            { term         = patt
            , predicate    = predicate
            , substitution = substitution
            }
      where
        Predicated { term = (), predicate, substitution } =
            childrenPredicateSubstitution

    simplifyIfNeeded
        :: ExpandedPattern level variable
        -> Simplifier (OrOfExpandedPattern level variable)
    simplifyIfNeeded toSimplify =
        if toSimplify == unchangedPatt
            then return (MultiOr.make [unchangedPatt])
            else
                reevaluateFunctions
                    tools
                    substitutionSimplifier
                    simplifier
                    axiomIdToEvaluator
                    toSimplify

evaluateSortInjection
    :: (MetaOrObject level, Ord (variable level))
    => MetadataTools level StepperAttributes
    -> Application level (StepPattern level variable)
    ->  ( Application level (StepPattern level variable)
        , SimplificationProof level
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
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        )
    => MetadataTools level StepperAttributes
    -- ^ Tools for finding additional information about patterns
    -- such as their sorts, whether they are constructors or hooked.
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions in patterns.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> ExpandedPattern level variable
    -- ^ Function evaluation result.
    -> Simplifier (OrOfExpandedPattern level variable)
reevaluateFunctions
    tools
    substitutionSimplifier
    termSimplifier
    axiomIdToEvaluator
    Predicated
        { term   = rewrittenPattern
        , predicate = rewritingCondition
        , substitution = rewrittenSubstitution
        }
  = do
    (pattOr , _proof) <- simplifyTerm' rewrittenPattern
    (mergedPatt, _proof) <-
        OrOfExpandedPattern.mergeWithPredicateSubstitution
            tools
            substitutionSimplifier
            termSimplifier
            axiomIdToEvaluator
            Predicated
                { term = ()
                , predicate = rewritingCondition
                , substitution = rewrittenSubstitution
                }
            pattOr
    (evaluatedPatt, _) <-
        MultiOr.traverseWithPairs
            (ExpandedPattern.simplifyPredicate
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
    ::  ( MetaOrObject level
        , Ord (variable level)
        , Show (variable level)
        , Unparse (variable level)
        , OrdMetaOrObject variable
        , ShowMetaOrObject variable
        , FreshVariable variable
        , SortedVariable variable
        )
    => MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level
    -> StepPatternSimplifier level
    -- ^ Evaluates functions in a pattern.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from axiom IDs to axiom evaluators
    -> PredicateSubstitution level variable
    -- ^ Condition and substitution to add.
    -> (AttemptedAxiom level variable, SimplificationProof level)
    -- ^ AttemptedAxiom to which the condition should be added.
    -> Simplifier (AttemptedAxiom level variable, SimplificationProof level)
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
        OrOfExpandedPattern.mergeWithPredicateSubstitution
            tools
            substitutionSimplifier
            simplifier
            axiomIdToEvaluator
            toMerge
            results
    (evaluatedRemainders, _proof) <-
        OrOfExpandedPattern.mergeWithPredicateSubstitution
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
