{-|
Module      : Kore.Step.Function.Evaluator
Description : Evaluates functions in a pattern.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Function.Evaluator
    ( evaluateFunctions
    ) where

import qualified Data.Foldable as Foldable
import           Data.List
                 ( nub )
import qualified Data.Map as Map
import           Data.Reflection
                 ( give )

import Data.Functor.Traversable
       ( fixTopDownVisitor )
import Kore.AST.Common
       ( Application (..), Id (..), Pattern (..), SortedVariable,
       SymbolOrAlias (..) )
import Kore.AST.MetaOrObject
import Kore.AST.MLPatterns
       ( MLBinderPatternClass (..), MLPatternClass (..),
       PatternLeveledFunction (..), applyPatternLeveledFunction )
import Kore.AST.PureML
       ( PureMLPattern, UnFixedPureMLPattern, asPurePattern )
import Kore.IndexedModule.MetadataTools
       ( MetadataTools (..) )
import Kore.Predicate.Predicate
       ( Predicate, pattern PredicateFalse, pattern PredicateTrue,
       makeTruePredicate )
import Kore.Step.Condition.Evaluator
       ( evaluateFunctionCondition )
import Kore.Step.ExpandedPattern as ExpandedPattern
       ( ExpandedPattern (..), bottom )
import Kore.Step.Function.Data
       ( ApplicationFunctionEvaluator (..), ConditionEvaluator (..),
       FunctionResultProof (..), PureMLPatternFunctionEvaluator (..) )
import Kore.Step.Function.Data as AttemptedFunction
       ( AttemptedFunction (..) )
import Kore.Step.StepperAttributes
       ( StepperAttributes (..) )
import Kore.Step.Substitution
       ( mergePredicatesAndSubstitutions )
import Kore.Unification.Unifier
       ( UnificationSubstitution )
import Kore.Variables.Fresh.IntCounter
       ( IntCounter )

{-|'evaluateFunctions' evaluates Kore functions (in a bottom-up manner).

It currently assumes that functions are unambiguous. Patterns that are not
applications of functional constructors may prevent function evaluation in
various ways.
-}
evaluateFunctions
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        )
    => MetadataTools level StepperAttributes
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level variable]
    -- ^ Map from a symbol's ID to all the function definitions for that symbol.
    -> PureMLPattern level variable
    -- ^ Pattern on which to evaluate functions
    -> IntCounter (ExpandedPattern level variable, FunctionResultProof level)
evaluateFunctions tools functionIdToEvaluator =
    fixTopDownVisitor
        (filterUnhandledPatterns tools)
        (evaluateLocalFunction
            tools
            (ConditionEvaluator conditionEvaluator)
            (PureMLPatternFunctionEvaluator functionEvaluator)
            functionIdToEvaluator
        )
  where
    conditionEvaluator =
        give (sortTools tools)
        $ evaluateFunctionCondition
            (PureMLPatternFunctionEvaluator functionEvaluator)
    functionEvaluator =
        evaluateFunctions tools functionIdToEvaluator

{-| 'FilterWrapper' adapts the natural result of filtering patterns to
the interface expected by 'applyPatternLeveledFunction'
-}
newtype FilterWrapper variable level = FilterWrapper
    { filterUnwrap
        :: Either
            (IntCounter
                (ExpandedPattern level variable, FunctionResultProof level)
            )
            (UnFixedPureMLPattern level variable)
    }

{-|'filterUnhandledPatterns' rejects everything that is not an application of
a constructor or a function.
-}
filterUnhandledPatterns
    :: MetaOrObject level
    => MetadataTools level StepperAttributes
    -> Pattern level variable (PureMLPattern level variable)
    -> Either
        (IntCounter (ExpandedPattern level variable, FunctionResultProof level))
        (UnFixedPureMLPattern level variable)
filterUnhandledPatterns metadataTools patt =
    filterUnwrap
        (applyPatternLeveledFunction
            PatternLeveledFunction
                { patternLeveledFunctionML = wrapUnchanged . mlPatternToPattern
                , patternLeveledFunctionMLBinder =
                    wrapUnchanged . mlBinderPatternToPattern
                , stringLeveledFunction = wrapUnchanged . StringLiteralPattern
                , charLeveledFunction = wrapUnchanged . CharLiteralPattern
                , domainValueLeveledFunction =
                    wrapUnchanged . DomainValuePattern
                , applicationLeveledFunction =
                    \ app@Application {applicationSymbolOrAlias = symbol} ->
                        if  isConstructor (attributes metadataTools symbol)
                            || isFunction (attributes metadataTools symbol)
                            then FilterWrapper $ Right $ ApplicationPattern app
                            else wrapUnchanged $ ApplicationPattern app
                , variableLeveledFunction = wrapUnchanged . VariablePattern
                }
            patt
        )
  where
    wrapUnchanged
        :: MetaOrObject level
        => Pattern level variable (PureMLPattern level variable)
        -> FilterWrapper variable level
    wrapUnchanged patt' =
        FilterWrapper $ Left $ return
            ( ExpandedPattern
                { term      = asPurePattern patt'
                , predicate = makeTruePredicate
                , substitution = []
                }
            , FunctionResultProof
            )

{-| 'EvaluationWrapper' adapts the natural result of evaluating functions
the interface expected by 'applyPatternLeveledFunction'
-}
newtype EvaluationWrapper variable level = EvaluationWrapper
    { evaluationUnwrap
        :: IntCounter (ExpandedPattern level variable, FunctionResultProof level)
    }

{-| 'evaluateLocalFunction' assumes that a pattern's children have been
evaluated and evaluates the pattern.
-}
evaluateLocalFunction
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        )
    => MetadataTools level StepperAttributes
    -> ConditionEvaluator level variable
    -> PureMLPatternFunctionEvaluator level variable
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level variable]
    -> Pattern
        level
        variable
        (IntCounter (ExpandedPattern level variable, FunctionResultProof level))
    -> IntCounter (ExpandedPattern level variable, FunctionResultProof level)
evaluateLocalFunction
    tools
    conditionEvaluator
    functionEvaluator
    symbolIdToEvaluators
    pattIF
  = do
    pattF <- sequenceA pattIF
    let

        (mergedCondition, childrenSubstitution, _) =
            -- TODO (virgil): Maybe make mergePredicatesAndSubstitutions take
            -- Foldable arguments.
            mergePredicatesAndSubstitutions
                tools
                (Foldable.toList (fmap (ExpandedPattern.predicate . fst) pattF))
                (Foldable.toList
                    (fmap (ExpandedPattern.substitution . fst) pattF)
                )
        normalPattern = fmap (ExpandedPattern.term . fst) pattF
        unchanged =
                returnUnchanged mergedCondition childrenSubstitution

        patternLeveledFunction = PatternLeveledFunction
            { patternLeveledFunctionML = unchanged . mlPatternToPattern
            , patternLeveledFunctionMLBinder =
                unchanged . mlBinderPatternToPattern
            , stringLeveledFunction =
                assertTrue mergedCondition
                . assertEmpty childrenSubstitution
                . returnUnchanged makeTruePredicate []
                . StringLiteralPattern
            , charLeveledFunction =
                assertTrue mergedCondition
                . assertEmpty childrenSubstitution
                . returnUnchanged makeTruePredicate []
                . CharLiteralPattern
            , domainValueLeveledFunction =
                assertTrue mergedCondition
                . assertEmpty childrenSubstitution
                . returnUnchanged makeTruePredicate []
                . DomainValuePattern
            , applicationLeveledFunction =
                evaluateApplication
                    tools
                    conditionEvaluator
                    functionEvaluator
                    symbolIdToEvaluators
                    mergedCondition
                    childrenSubstitution
            , variableLeveledFunction = unchanged . VariablePattern
            }

    evaluationUnwrap
        ( applyPatternLeveledFunction
            patternLeveledFunction
            normalPattern
        )
  where
    returnUnchanged
        :: Predicate level variable
        -> UnificationSubstitution level variable
        -> Pattern level variable (PureMLPattern level variable)
        -> EvaluationWrapper variable level
    returnUnchanged condition substitution' patt =
        EvaluationWrapper $ return
            ( ExpandedPattern
                { term      = asPurePattern patt
                , predicate = condition
                , substitution = substitution'
                }
            , FunctionResultProof
            )
    assertTrue :: Predicate level variable -> a -> a
    assertTrue PredicateTrue x = x
    assertTrue _ _             = error "Expecting the condition to be true."
    assertEmpty :: [elem] -> a -> a
    assertEmpty [] x = x
    assertEmpty _ _  = error "Expecting an empty list."

{-| 'evaluateApplication' - evaluates functions on an application pattern.
-}
evaluateApplication
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level)
        )
    => MetadataTools level StepperAttributes
    -> ConditionEvaluator level variable
    -- ^ Evaluates conditions
    -> PureMLPatternFunctionEvaluator level variable
    -- ^ Evaluates functions.
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level variable]
    -- ^ Map from symbol IDs to defined functions
    -> Predicate level variable
    -- ^ Aggregated children condition.
    -> UnificationSubstitution level variable
    -- ^ Aggregated children substitution.
    -> Application level (PureMLPattern level variable)
    -- ^ The pattern to be evaluated
    -> EvaluationWrapper variable level
evaluateApplication
    tools
    conditionEvaluator
    functionEvaluator
    symbolIdToEvaluator
    childrenCondition
    childrenSubstitution
    app@Application
        { applicationSymbolOrAlias = SymbolOrAlias
            -- TODO(virgil): Should we use the symbolOrAliasParams? Should
            -- not matter for correctness since each function can reject the
            -- input, and it would be more complex to handle them properly.
            { symbolOrAliasConstructor = symbolId }
        }
  = EvaluationWrapper $
        case Map.lookup symbolId symbolIdToEvaluator of
            Nothing -> return unchanged
            Just evaluators -> do
                results <- mapM (applyEvaluator app) evaluators
                mergedResults <-
                    mapM
                        (mergeWithConditionAndSubstitution
                            tools
                            conditionEvaluator
                            childrenCondition
                            childrenSubstitution
                        )
                        results
                -- After removing N/A results and duplicates we expect at most
                -- one result, i.e. we don't handle ambiguity
                -- TODO(virgil): nub is O(n^2), should do better than that.
                case nub (filter notBottom mergedResults) of
                    [] -> return bottom'
                    [(AttemptedFunction.NotApplicable, _)] ->
                        return unchanged
                    [(AttemptedFunction.Applied functionResult, proof)] ->
                        return (functionResult, proof)
                    (_ : _ : _) -> error "Not implemented yet."
  where
    unchanged =
        ( ExpandedPattern
            { term      = asPurePattern $ ApplicationPattern app
            , predicate = childrenCondition
            , substitution = childrenSubstitution
            }
        , FunctionResultProof
        )
    bottom' = (ExpandedPattern.bottom, FunctionResultProof)
    applyEvaluator app' (ApplicationFunctionEvaluator evaluator) =
        evaluator
            tools
            conditionEvaluator
            functionEvaluator
            app'
    notBottom =
        \case
            (AttemptedFunction.Applied
                ExpandedPattern {predicate = PredicateFalse}
             , _
             ) -> False
            _ -> True

{-| 'mergeWithCondition' ands the given condition to the given function
evaluation.
-}
mergeWithConditionAndSubstitution
    ::  ( MetaOrObject level
        , SortedVariable variable
        , Show (variable level)
        , Ord (variable level))
    => MetadataTools level StepperAttributes
    -> ConditionEvaluator level variable
    -- ^ Can evaluate conditions.
    -> Predicate level variable
    -- ^ Condition to add.
    -> UnificationSubstitution level variable
    -- ^ Substitution to add.
    -> (AttemptedFunction level variable, FunctionResultProof level)
    -- ^ AttemptedFunction level variable to which the condition should be added.
    -> IntCounter
        (AttemptedFunction level variable, FunctionResultProof level)
mergeWithConditionAndSubstitution _ _ _ _ (AttemptedFunction.NotApplicable, _) =
    return (AttemptedFunction.NotApplicable, FunctionResultProof)
mergeWithConditionAndSubstitution
    tools
    (ConditionEvaluator conditionEvaluator)
    conditionToMerge
    substitutionToMerge
    (AttemptedFunction.Applied functionResult, _)
  = let
        (mergedCondition, mergedSubstitution, _) =
            mergePredicatesAndSubstitutions
                tools
                [ExpandedPattern.predicate functionResult, conditionToMerge]
                [ ExpandedPattern.substitution functionResult
                , substitutionToMerge
                ]
    in do
        evaluatedCondition <- conditionEvaluator mergedCondition
        case evaluatedCondition of
            (PredicateFalse, _) -> return
                ( AttemptedFunction.Applied ExpandedPattern.bottom
                , FunctionResultProof
                )
            _ -> return
                ( AttemptedFunction.Applied functionResult
                    { predicate = mergedCondition
                    , substitution = mergedSubstitution
                    }
                , FunctionResultProof
                )
