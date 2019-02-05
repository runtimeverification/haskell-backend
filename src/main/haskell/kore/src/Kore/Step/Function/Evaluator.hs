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
    ( applyFirstSimplifierThatWorks
    , evaluateApplication
    -- TODO(virgil): Move all exports except evaluateApplication to
    -- EvaluationStrategy.hs.
    , evaluateWithDefinitionAxioms
    , AcceptsMultipleResults (..)
    , evaluateBuiltin
    ) where

import           Control.Exception
                 ( assert )
import           Control.Monad
                 ( when )
import qualified Data.Map as Map
import           Data.Maybe
                 ( isJust )
import           Data.Reflection
                 ( give )
import qualified Data.Text as Text

import           Kore.AST.Pure
import           Kore.AST.Valid
import           Kore.Debug
import           Kore.IndexedModule.MetadataTools
                 ( MetadataTools (..) )
import           Kore.Predicate.Predicate
                 ( makeTruePredicate )
import           Kore.Step.AxiomPatterns
                 ( EqualityRule (EqualityRule) )
import           Kore.Step.BaseStep
                 ( OrStepResult (OrStepResult),
                 UnificationProcedure (UnificationProcedure),
                 stepWithRemaindersForUnifier )
import qualified Kore.Step.BaseStep as OrStepResult
                 ( OrStepResult (..) )
import           Kore.Step.ExpandedPattern
                 ( ExpandedPattern, PredicateSubstitution, Predicated (..) )
import qualified Kore.Step.ExpandedPattern as ExpandedPattern
                 ( fromPurePattern )
import           Kore.Step.Function.Data
                 ( AttemptedAxiomResults (AttemptedAxiomResults),
                 BuiltinAndAxiomSimplifier (..), BuiltinAndAxiomSimplifierMap )
import           Kore.Step.Function.Data as AttemptedAxiom
                 ( AttemptedAxiom (..) )
import           Kore.Step.Function.Data as AttemptedAxiomResults
                 ( AttemptedAxiomResults (..) )
import           Kore.Step.Function.Matcher
                 ( unificationWithAppMatchOnTop )
import qualified Kore.Step.Merging.OrOfExpandedPattern as OrOfExpandedPattern
                 ( mergeWithPredicateSubstitution )
import           Kore.Step.OrOfExpandedPattern
                 ( OrOfExpandedPattern )
import qualified Kore.Step.OrOfExpandedPattern as OrOfExpandedPattern
                 ( extractPatterns, flatten, isFalse, make, merge,
                 traverseWithPairs )
import           Kore.Step.Pattern
import           Kore.Step.Simplification.Data
                 ( PredicateSubstitutionSimplifier, SimplificationProof (..),
                 Simplifier, StepPatternSimplifier (..) )
import qualified Kore.Step.Simplification.ExpandedPattern as ExpandedPattern
import           Kore.Step.StepperAttributes
                 ( Hook (..), StepperAttributes (..), isSortInjection_ )
import           Kore.Unparser
import           Kore.Variables.Fresh

{-|Describes whether simplifiers are allowed to return multiple results or not.
-}
data AcceptsMultipleResults = WithMultipleResults | OnlyOneResult

{-|Converts 'AcceptsMultipleResults' to Bool.
-}
acceptsMultipleResults :: AcceptsMultipleResults -> Bool
acceptsMultipleResults WithMultipleResults = True
acceptsMultipleResults OnlyOneResult = False

{-| 'evaluateApplication' - evaluates functions on an application pattern.
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
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions.
    -> BuiltinAndAxiomSimplifierMap level
    -- ^ Map from symbol IDs to defined functions
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
    symbolIdToEvaluator
    childrenPredicateSubstitution
    (valid :< app)
  =
    case Map.lookup symbolId symbolIdToEvaluator of
        Nothing
          | give tools isSortInjection_ appHead ->
            evaluateSortInjection tools unchangedOr app
          | Just hook <- getAppHookString
          , not(null symbolIdToEvaluator) ->
            error
                (   "Attempting to evaluate unimplemented hooked operation "
                ++  hook ++ ".\nSymbol: " ++ show (getId symbolId)
                )
          | otherwise ->
            return unchanged
        Just (BuiltinAndAxiomSimplifier evaluator) ->
            traceNonErrorMonad
                D_Function_evaluateApplication
                [debugArg "symbolId" (getId symbolId)]
            $ do
                (result, proof) <-
                    evaluator
                        tools
                        substitutionSimplifier
                        simplifier
                        appPurePattern
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
                                        OrOfExpandedPattern.flatten simplified
                                    , remainders = orRemainders
                                    }
                                )
                (merged, _proof) <- mergeWithConditionAndSubstitution
                    tools
                    substitutionSimplifier
                    simplifier
                    childrenPredicateSubstitution
                    (flattened, proof)
                case merged of
                    AttemptedAxiom.NotApplicable -> return unchanged
                    AttemptedAxiom.Applied AttemptedAxiomResults
                        { results, remainders } ->
                            return
                                ( OrOfExpandedPattern.merge results remainders
                                , SimplificationProof
                                )
  where
    Application { applicationSymbolOrAlias = appHead } = app
    SymbolOrAlias { symbolOrAliasConstructor = symbolId } = appHead

    appPurePattern = asPurePattern (valid :< ApplicationPattern app)

    unchangedPatt =
        case childrenPredicateSubstitution of
            Predicated { predicate, substitution } ->
                Predicated
                    { term         = appPurePattern
                    , predicate    = predicate
                    , substitution = substitution
                    }
    unchangedOr = OrOfExpandedPattern.make [unchangedPatt]
    unchanged = (unchangedOr, SimplificationProof)

    getAppHookString =
        Text.unpack <$> (getHook . hook . symAttributes tools) appHead

    simplifyIfNeeded
        :: ExpandedPattern level variable
        -> Simplifier (OrOfExpandedPattern level variable)
    simplifyIfNeeded patt =
        if patt == unchangedPatt
            then return (OrOfExpandedPattern.make [unchangedPatt])
            else
                reevaluateFunctions
                    tools
                    substitutionSimplifier
                    simplifier
                    patt

evaluateBuiltin
    :: forall variable level
    .   ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , SortedVariable variable
        , Show (variable level)
        , Show (variable Object)
        , Unparse (variable level)
        , ShowMetaOrObject variable
        )
    => BuiltinAndAxiomSimplifier level
    -> MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -> StepPattern level variable
    -> Simplifier
        (AttemptedAxiom level variable, SimplificationProof level)
evaluateBuiltin
    (BuiltinAndAxiomSimplifier builtinEvaluator)
    tools
    substitutionSimplifier
    simplifier
    patt
  = do
    (result, _proof) <-
        builtinEvaluator
            tools
            substitutionSimplifier
            simplifier
            patt
    case result of
        AttemptedAxiom.NotApplicable
          | isPattConcrete
          , Just hook <- getAppHookString ->
            error
                (   "Expecting hook " ++ hook
                ++  " to reduce concrete pattern\n\t"
                ++ show patt
                )
          | otherwise ->
            return (AttemptedAxiom.NotApplicable, SimplificationProof)
        AttemptedAxiom.Applied _ -> return (result, SimplificationProof)
  where
    isPattConcrete = traceFunction D_Function_evaluateApplication [] $ isJust (asConcretePurePattern patt)
    appHead = case patt of
        App_ head0 _children -> head0
        _ -> error
            ("Expected an application pattern, but got " ++ show patt ++ ".")
    -- TODO(virgil): Send this from outside after replacing `These` as a
    -- representation for application evaluators.
    getAppHookString = traceFunction D_Function_evaluateApplication [] $
        Text.unpack <$> (getHook . hook . symAttributes tools) appHead

applyFirstSimplifierThatWorks
    :: forall variable level
    .   ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , SortedVariable variable
        , Show (variable level)
        , Show (variable Object)
        , Unparse (variable level)
        , ShowMetaOrObject variable
        )
    => [BuiltinAndAxiomSimplifier level]
    -> AcceptsMultipleResults
    -> MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -> StepPattern level variable
    -> Simplifier
        (AttemptedAxiom level variable, SimplificationProof level)
applyFirstSimplifierThatWorks [] _ _ _ _ _ =
    return
        ( AttemptedAxiom.NotApplicable
        , SimplificationProof
        )
applyFirstSimplifierThatWorks
    (BuiltinAndAxiomSimplifier evaluator : evaluators)
    multipleResults
    tools
    substitutionSimplifier
    simplifier
    patt
  = do
    (applicationResult, _proof) <-
        evaluator tools substitutionSimplifier simplifier patt

    case applicationResult of
        AttemptedAxiom.Applied AttemptedAxiomResults
            { results = orResults
            , remainders = orRemainders
            } -> do
                when
                    (length (OrOfExpandedPattern.extractPatterns orResults) > 1
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
                    (not (OrOfExpandedPattern.isFalse orRemainders)
                    && not (acceptsMultipleResults multipleResults)
                    )
                    -- It's not obvious that we should accept simplifications
                    -- that change only a part of the configuration, since
                    -- that will probably make things more complicated.
                    --
                    -- Until we have a clear example that this can actually
                    -- happen, we throw an error.
                    (error
                        (  "Unexpected simplification result with remainder: "
                        ++ show applicationResult
                        )
                    )
                return (applicationResult, SimplificationProof)
        AttemptedAxiom.NotApplicable ->
            applyFirstSimplifierThatWorks
                evaluators
                multipleResults
                tools
                substitutionSimplifier
                simplifier
                patt

evaluateWithDefinitionAxioms
    :: forall variable level
    .   ( FreshVariable variable
        , MetaOrObject level
        , Ord (variable level)
        , OrdMetaOrObject variable
        , SortedVariable variable
        , Show (variable level)
        , Show (variable Object)
        , Unparse (variable level)
        , ShowMetaOrObject variable
        )
    => [EqualityRule level]
    -> MetadataTools level StepperAttributes
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -> StepPattern level variable
    -> Simplifier
        (AttemptedAxiom level variable, SimplificationProof level)
evaluateWithDefinitionAxioms
    definitionRules tools substitutionSimplifier simplifier patt
  = do
    let
        expanded :: ExpandedPattern level variable
        expanded = ExpandedPattern.fromPurePattern patt

    (OrStepResult { rewrittenPattern, remainder }, _proof) <-
        stepWithRemaindersForUnifier
            tools
            (UnificationProcedure unificationWithAppMatchOnTop)
            substitutionSimplifier
            (map (\ (EqualityRule rule) -> rule) definitionRules)
            expanded
    let
        remainderResults :: [ExpandedPattern level variable]
        remainderResults = OrOfExpandedPattern.extractPatterns remainder

        simplifyPredicate
            :: ExpandedPattern level variable
            -> Simplifier
                (ExpandedPattern level variable, SimplificationProof level)
        simplifyPredicate =
            ExpandedPattern.simplifyPredicate
                tools
                substitutionSimplifier
                simplifier

    simplifiedRemainderList <- mapM simplifyPredicate remainderResults
    let
        simplifiedRemainderResults :: [ExpandedPattern level variable]
        (simplifiedRemainderResults, _proofs) =
            unzip simplifiedRemainderList
    return
        ( AttemptedAxiom.Applied AttemptedAxiomResults
            { results = rewrittenPattern
            , remainders = OrOfExpandedPattern.make simplifiedRemainderResults
            }
        , SimplificationProof
        )

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
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions in patterns.
    -> ExpandedPattern level variable
    -- ^ Function evaluation result.
    -> Simplifier (OrOfExpandedPattern level variable)
reevaluateFunctions
    tools
    substitutionSimplifier
    wrappedSimplifier@(StepPatternSimplifier simplifier)
    Predicated
        { term   = rewrittenPattern
        , predicate = rewritingCondition
        , substitution = rewrittenSubstitution
        }
  = do
    (pattOr , _proof) <-
        simplifier substitutionSimplifier rewrittenPattern
    (mergedPatt, _proof) <-
        OrOfExpandedPattern.mergeWithPredicateSubstitution
            tools
            substitutionSimplifier
            wrappedSimplifier
            Predicated
                { term = ()
                , predicate = rewritingCondition
                , substitution = rewrittenSubstitution
                }
            pattOr
    (evaluatedPatt, _) <-
        OrOfExpandedPattern.traverseWithPairs
            (ExpandedPattern.simplifyPredicate
                tools substitutionSimplifier wrappedSimplifier
            )
            mergedPatt
    return evaluatedPatt

evaluateSortInjection
    :: (MetaOrObject level, Ord (variable level))
    => MetadataTools level StepperAttributes
    -> OrOfExpandedPattern level variable
    -> Application level (StepPattern level variable)
    -> Simplifier (OrOfExpandedPattern level variable, SimplificationProof level)
evaluateSortInjection tools unchanged ap = case apChild of
    (App_ apHeadChild grandChildren)
      | give tools isSortInjection_ apHeadChild ->
        let
            [fromSort', toSort'] = symbolOrAliasParams apHeadChild
            apHeadNew = updateSortInjectionSource apHead fromSort'
        in
            assert (toSort' == fromSort) $
            return
                ( OrOfExpandedPattern.make
                    [ Predicated
                        { term = apHeadNew grandChildren
                        , predicate = makeTruePredicate
                        , substitution = mempty
                        }
                    ]
                , SimplificationProof
                )
    _ -> return (unchanged, SimplificationProof)
  where
    apHead = applicationSymbolOrAlias ap
    [fromSort, _] = symbolOrAliasParams apHead
    [apChild] = applicationChildren ap
    updateSortInjectionSource head1 fromSort1 =
        mkApp toSort1 head1 { symbolOrAliasParams = [fromSort1, toSort1] }
      where
        [_, toSort1] = symbolOrAliasParams head1

{-| 'mergeWithCondition' ands the given condition-substitution to the given
function evaluation.
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
    -> PredicateSubstitutionSimplifier level Simplifier
    -> StepPatternSimplifier level variable
    -- ^ Evaluates functions in a pattern.
    -> PredicateSubstitution level variable
    -- ^ Condition and substitution to add.
    -> (AttemptedAxiom level variable, SimplificationProof level)
    -- ^ AttemptedAxiom to which the condition should be added.
    -> Simplifier (AttemptedAxiom level variable, SimplificationProof level)
mergeWithConditionAndSubstitution
    _ _ _ _ (AttemptedAxiom.NotApplicable, _proof)
  =
    return (AttemptedAxiom.NotApplicable, SimplificationProof)
mergeWithConditionAndSubstitution
    tools
    substitutionSimplifier
    simplifier
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
            toMerge
            results
    (evaluatedRemainders, _proof) <-
        OrOfExpandedPattern.mergeWithPredicateSubstitution
            tools
            substitutionSimplifier
            simplifier
            toMerge
            remainders
    return
        ( AttemptedAxiom.Applied AttemptedAxiomResults
            { results = evaluatedResults, remainders = evaluatedRemainders }
        , SimplificationProof
        )
