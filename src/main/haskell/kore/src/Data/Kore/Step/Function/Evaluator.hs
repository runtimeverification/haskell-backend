{-|
Module      : Data.Kore.Step.Function.Evaluator
Description : Evaluates functions in a pattern.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Data.Kore.Step.Function.Evaluator
    ( evaluateFunctions
    ) where

import           Data.List                             (nub)
import qualified Data.Map                              as Map

import           Data.Kore.AST.Common                  (Application (..),
                                                        Id (..), Pattern (..),
                                                        SymbolOrAlias (..),
                                                        Variable)
import           Data.Kore.AST.MLPatterns              (MLBinderPatternClass (..),
                                                        MLPatternClass (..),
                                                        PatternLeveledFunction (..),
                                                        applyPatternLeveledFunction)
import           Data.Kore.AST.PureML                  (CommonPurePattern,
                                                        UnFixedPureMLPattern,
                                                        asPurePattern)
import           Data.Kore.FixTraversals               (fixTopDownVisitor)
import           Data.Kore.IndexedModule.MetadataTools (MetadataTools (..))
import           Data.Kore.Step.Condition.Condition    (ConditionProof (..),
                                                        ConditionSort (..),
                                                        EvaluatedCondition (..),
                                                        makeEvaluatedAnd)
import           Data.Kore.Step.Condition.Evaluator    (evaluateFunctionCondition)
import           Data.Kore.Step.Function.Data          (ApplicationFunctionEvaluator (..),
                                                        AttemptedFunctionResult (..),
                                                        CommonPurePatternFunctionEvaluator (..),
                                                        ConditionEvaluator (..),
                                                        FunctionResult (..),
                                                        FunctionResultProof (..))
import           Data.Kore.Variables.Fresh.IntCounter  (IntCounter)

{-|'evaluateFunctions' evaluates Kore functions (in a bottom-up manner).

It currently assumes that functions are unambiguous. Patterns that are not
applications of functional constructors may prevent function evaluation in
various ways.
-}
evaluateFunctions
    :: MetadataTools level
    -- ^ Defines what is a function and what is not.
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level]
    -- ^ Map from a symbol's ID to all the function definitions for that symbol.
    -> ConditionSort level
    -- ^ Sort used for conditions. This function assumes that all conditions
    -- have this sort and will use it to create new conditions.
    -> CommonPurePattern level
    -- ^ Pattern on which to evaluate functions
    -> IntCounter (FunctionResult level, FunctionResultProof level)
evaluateFunctions metadataTools functionIdToEvaluator conditionSort =
    fixTopDownVisitor
        (filterUnhandledPatterns metadataTools)
        (evaluateLocalFunction
            (ConditionEvaluator conditionEvaluator)
            (CommonPurePatternFunctionEvaluator functionEvaluator)
            functionIdToEvaluator
            conditionSort)
  where
    conditionEvaluator =
        evaluateFunctionCondition
            (CommonPurePatternFunctionEvaluator functionEvaluator)
            conditionSort
    functionEvaluator =
        evaluateFunctions metadataTools functionIdToEvaluator conditionSort

{--| 'FilterWrapper' adapts the natural result of filtering patterns to
the interface expected by 'applyPatternLeveledFunction'
--}
newtype FilterWrapper level = FilterWrapper
    { filterUnwrap
        :: Either
            (IntCounter (FunctionResult level, FunctionResultProof level))
            (UnFixedPureMLPattern level Variable)
    }

{--|'filterUnhandledPatterns' rejects everything that is not an application of
a constructor or a function.
--}
filterUnhandledPatterns
    :: MetadataTools level
    -> Pattern level Variable (CommonPurePattern level)
    -> Either
        (IntCounter (FunctionResult level, FunctionResultProof level))
        (UnFixedPureMLPattern level Variable)
filterUnhandledPatterns metadataTools patt =
    filterUnwrap
        (applyPatternLeveledFunction
            PatternLeveledFunction
                { patternLeveledFunctionML = wrapUnchanged . mlPatternToPattern
                , patternLeveledFunctionMLBinder =
                    wrapUnchanged . mlBinderPatternToPattern
                , stringLeveledFunction = wrapUnchanged . StringLiteralPattern
                , charLeveledFunction = wrapUnchanged . CharLiteralPattern
                , applicationLeveledFunction =
                    \ app@Application {applicationSymbolOrAlias = symbol} ->
                        if  isConstructor metadataTools symbol
                            || isFunction metadataTools symbol
                            then FilterWrapper $ Right $ ApplicationPattern app
                            else wrapUnchanged $ ApplicationPattern app
                , variableLeveledFunction = wrapUnchanged . VariablePattern
                }
            patt
        )
  where
    wrapUnchanged
        :: Pattern level Variable (CommonPurePattern level)
        -> FilterWrapper level
    wrapUnchanged patt' =
        FilterWrapper $ Left $ return
            ( FunctionResult
                { functionResultPattern   = asPurePattern patt'
                , functionResultCondition = ConditionTrue
                }
            , FunctionResultProof
            )

{--| 'EvaluationWrapper' adapts the natural result of evaluating functions
the interface expected by 'applyPatternLeveledFunction'
--}
newtype EvaluationWrapper level = EvaluationWrapper
    { evaluationUnwrap
        :: IntCounter (FunctionResult level, FunctionResultProof level)
    }

{--| 'evaluateLocalFunction' assumes that a pattern's children have been
evaluated and evaluates the pattern.
--}
evaluateLocalFunction
    :: ConditionEvaluator level
    -> CommonPurePatternFunctionEvaluator level
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level]
    -> ConditionSort level
    -> Pattern
        level
        Variable
        (IntCounter (FunctionResult level, FunctionResultProof level))
    -> IntCounter (FunctionResult level, FunctionResultProof level)
evaluateLocalFunction
    conditionEvaluator
    functionEvaluator
    symbolIdToEvaluators
    conditionSort
    pattIF
  = do
    pattF <- sequenceA pattIF
    let
        (childrenCondition, _) =
            foldr
                (andChildrenConditions conditionSort)
                (ConditionTrue, FunctionResultProof)
                (fmap (functionResultCondition . fst) pattF)
        normalPattern = fmap (functionResultPattern . fst) pattF
        unchanged = returnUnchanged childrenCondition
    evaluationUnwrap
        ( applyPatternLeveledFunction
            PatternLeveledFunction
                { patternLeveledFunctionML = unchanged . mlPatternToPattern
                , patternLeveledFunctionMLBinder =
                    unchanged . mlBinderPatternToPattern
                , stringLeveledFunction =
                    assertTrue childrenCondition
                    . returnUnchanged ConditionTrue
                    . StringLiteralPattern
                , charLeveledFunction =
                    assertTrue childrenCondition
                    . returnUnchanged ConditionTrue
                    . CharLiteralPattern
                , applicationLeveledFunction =
                    evaluateApplication
                        conditionEvaluator
                        functionEvaluator
                        symbolIdToEvaluators
                        conditionSort
                        childrenCondition
                , variableLeveledFunction = unchanged . VariablePattern
                }
            normalPattern
        )
  where
    returnUnchanged
        :: EvaluatedCondition level
        -> Pattern level Variable (CommonPurePattern level)
        -> EvaluationWrapper level
    returnUnchanged condition patt =
        EvaluationWrapper $ return
            ( FunctionResult
                { functionResultPattern   = asPurePattern patt
                , functionResultCondition = condition
                }
            , FunctionResultProof
            )
    assertTrue :: EvaluatedCondition level -> a -> a
    assertTrue ConditionTrue x = x
    assertTrue _ _             = error "Expecting the condition to be true."

{--| 'andChildrenConditions' combines two children's conditions.
--}
andChildrenConditions
    :: ConditionSort level
    -- ^ Sort used for conditions. This function assumes that all conditions
    -- have this sort and will use it to create new conditions.
    -> EvaluatedCondition level
    -> (EvaluatedCondition level, FunctionResultProof level)
    -> (EvaluatedCondition level, FunctionResultProof level)
andChildrenConditions conditionSort first (second, _) =
    (fst (makeEvaluatedAnd conditionSort first second), FunctionResultProof)

{--| 'evaluateApplication' - evaluates functions on an application pattern.
--}
evaluateApplication
    :: ConditionEvaluator level
    -- ^ Evaluates conditions
    -> CommonPurePatternFunctionEvaluator level
    -- ^ Evaluates functions.
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level]
    -- ^ Map from symbol IDs to defined functions
    -> ConditionSort level
    -- ^ Sort used for conditions. This function assumes that all conditions
    -- have this sort and will use it to create new conditions.
    -> EvaluatedCondition level
    -- ^ Aggregated children condition.
    -> Application level (CommonPurePattern level)
    -- ^ The pattern to be evaluated
    -> EvaluationWrapper level
evaluateApplication
    conditionEvaluator
    functionEvaluator
    symbolIdToEvaluator
    conditionSort
    childrenCondition
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
                        (mergeWithCondition
                            conditionEvaluator conditionSort childrenCondition
                        )
                        results
                -- After removing N/A results and duplicates we expect at most
                -- one result, i.e. we don't handle ambiguity
                -- TODO(virgil): nub is O(n^2), should do better than that.
                case nub (filter notNotApplicable mergedResults) of
                    [] -> return unchanged
                    [(AttemptedFunctionResultNotApplicable, _)] ->
                        error "Should not reach this line."
                    [(AttemptedFunctionResultSymbolic condition, proof)] ->
                        return
                            ( FunctionResult
                                { functionResultPattern =
                                    asPurePattern $ ApplicationPattern app
                                , functionResultCondition = condition
                                }
                            , proof
                            )
                    [(AttemptedFunctionResultApplied functionResult, proof)] ->
                        return (functionResult, proof)
                    (_ : _ : _) -> error "Not implemented yet."
  where
    unchanged =
        ( FunctionResult
            { functionResultPattern   = asPurePattern $ ApplicationPattern app
            , functionResultCondition = childrenCondition
            }
        , FunctionResultProof
        )
    applyEvaluator app' (ApplicationFunctionEvaluator evaluator) =
        evaluator
            conditionEvaluator
            functionEvaluator
            app'
    notNotApplicable =
        \case
            (AttemptedFunctionResultNotApplicable, _) -> False
            _ -> True

{--| 'mergeWithCondition' ands the given condition to the given function
evaluation.
--}
mergeWithCondition
    :: ConditionEvaluator level
    -- ^ Can evaluate conditions.
    -> ConditionSort level
    -- ^ Sort used for conditions. This function assumes that all conditions
    -- have this sort and will use it to create new conditions.
    -> EvaluatedCondition level
    -- ^ Condition to add.
    -> (AttemptedFunctionResult level, FunctionResultProof level)
    -- ^ AttemptedFunctionResult to which the condition should be added.
    -> IntCounter (AttemptedFunctionResult level, FunctionResultProof level)
mergeWithCondition _ _ _ (AttemptedFunctionResultNotApplicable, _) =
    return (AttemptedFunctionResultNotApplicable, FunctionResultProof)
mergeWithCondition
    conditionEvaluator
    conditionSort
    toMerge
    (AttemptedFunctionResultSymbolic condition, _)
  = do
    (mergedCondition, _) <-
        mergeConditions conditionEvaluator conditionSort condition toMerge
    case mergedCondition of
        ConditionFalse ->
            return (AttemptedFunctionResultNotApplicable, FunctionResultProof)
        _              ->
            return
                ( AttemptedFunctionResultSymbolic mergedCondition
                , FunctionResultProof
                )
mergeWithCondition
    conditionEvaluator
    conditionSort
    toMerge
    (AttemptedFunctionResultApplied functionResult, _)
  = do
    mergedCondition <-
        mergeConditions
            conditionEvaluator
            conditionSort
            (functionResultCondition functionResult)
            toMerge
    case mergedCondition of
        (ConditionFalse, _) ->
            return (AttemptedFunctionResultNotApplicable, FunctionResultProof)
        _ -> return
            ( AttemptedFunctionResultApplied functionResult
                {functionResultCondition = fst mergedCondition}
            , FunctionResultProof
            )

{--| 'mergeConditions' merges two conditions with an 'and'.
--}
mergeConditions
    :: ConditionEvaluator level
    -- ^ Can evaluate conditions.
    -> ConditionSort level
    -- ^ Sort used for conditions. This function assumes that all conditions
    -- have this sort and will use it to create new conditions.
    -> EvaluatedCondition level
    -> EvaluatedCondition level
    -> IntCounter (EvaluatedCondition level, ConditionProof level)
mergeConditions _ conditionSort first second =
    return $ makeEvaluatedAnd conditionSort first second
    -- TODO(virgil): Should be something like:
    -- conditionEvaluator (makeEvaluatedAnd conditionSort first second)
    -- but, right now, we don't have conditions which are partly satisfiable.
