{-# LANGUAGE GADTs      #-}
{-# LANGUAGE LambdaCase #-}
{-|
Module      : Data.Kore.Step.Function.Evaluator
Description : Evaluates functions in a pattern
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
                                                        Sort (..),
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
import           Data.Kore.Step.Condition.Condition    (EvaluatedCondition (..),
                                                        makeEvaluatedAnd)
import           Data.Kore.Step.Condition.Evaluator    (evaluateFunctionCondition)
import           Data.Kore.Step.Function.Data          (ApplicationFunctionEvaluator (..),
                                                        CommonPurePatternFunctionEvaluator (..),
                                                        ConditionEvaluator (..),
                                                        FunctionEvaluation (..),
                                                        FunctionResult (..))
import           Data.Kore.Variables.Fresh.IntCounter  (IntCounter)

import           Debug.Trace

multiTrace :: [String] -> a -> a
multiTrace [] a     = a
multiTrace (x:xs) a = trace x $ multiTrace xs a

evaluateFunctions
    :: MetadataTools level
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level]
    -> Sort level
    -> CommonPurePattern level
    -> IntCounter (FunctionResult level)
evaluateFunctions metadataTools functionIdToEvaluator conditionSort =
    trace "Evaluate functions" $
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

newtype FilterWrapper level = FilterWrapper
    { filterUnwrap :: Either (IntCounter (FunctionResult level)) (UnFixedPureMLPattern level Variable)
    }

filterUnhandledPatterns
    :: MetadataTools level
    -> Pattern level Variable (CommonPurePattern level)
    -> Either
        (IntCounter (FunctionResult level))
        (UnFixedPureMLPattern level Variable)
filterUnhandledPatterns metadataTools patt =
    filterUnwrap
        (applyPatternLeveledFunction
            PatternLeveledFunction
                { patternLeveledFunctionML = wrapUnchanged . mlPatternToPattern
                , patternLeveledFunctionMLBinder = wrapUnchanged . mlBinderPatternToPattern
                , stringLeveledFunction = wrapUnchanged . StringLiteralPattern
                , charLeveledFunction = wrapUnchanged . CharLiteralPattern
                , applicationLeveledFunction =
                    \ app@Application {applicationSymbolOrAlias = symbol} ->
                        trace ("Hi " ++ getId (symbolOrAliasConstructor symbol)) $
                        if isConstructor metadataTools symbol || isFunction metadataTools symbol
                            then trace "Right" $ FilterWrapper $ Right $ ApplicationPattern app
                            else trace "Left" $ wrapUnchanged $ ApplicationPattern app
                , variableLeveledFunction = wrapUnchanged . VariablePattern
                }
            patt
        )
  where
    wrapUnchanged
        :: Pattern level Variable (CommonPurePattern level)
        -> FilterWrapper level
    wrapUnchanged patt' =
        FilterWrapper $ Left $ return FunctionResult
            { functionResultPattern   = asPurePattern patt'
            , functionResultCondition = ConditionTrue
            }

newtype EvaluationWrapper level = EvaluationWrapper
    { evaluationUnwrap :: IntCounter (FunctionResult level) }

evaluateLocalFunction
    :: ConditionEvaluator level
    -> CommonPurePatternFunctionEvaluator level
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level]
    -> Sort level -- TODO: Wrap in a type.
    -> Pattern level Variable (IntCounter (FunctionResult level))
    -> IntCounter (FunctionResult level)
evaluateLocalFunction
    conditionEvaluator
    functionEvaluator
    symbolIdToEvaluators
    conditionSort
    pattIF
  = do
    pattF <- sequenceA pattIF
    let
        childrenCondition =
            foldr
                (makeEvaluatedAnd conditionSort)
                ConditionTrue
                (fmap functionResultCondition pattF)
        normalPattern = fmap functionResultPattern pattF
        unchanged = returnUnchanged childrenCondition
    evaluationUnwrap
        ( applyPatternLeveledFunction
            PatternLeveledFunction
                { patternLeveledFunctionML = unchanged . mlPatternToPattern
                , patternLeveledFunctionMLBinder = unchanged . mlBinderPatternToPattern
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
        EvaluationWrapper $ return FunctionResult
            { functionResultPattern   = asPurePattern patt
            , functionResultCondition = condition
            }
    assertTrue :: EvaluatedCondition level -> a -> a
    assertTrue ConditionTrue x = x
    assertTrue _ _             = error "Expecting the condition to be true."

evaluateApplication
    :: ConditionEvaluator level
    -> CommonPurePatternFunctionEvaluator level
    -> Map.Map (Id level) [ApplicationFunctionEvaluator level]
    -> Sort level
    -> EvaluatedCondition level
    -> Application level (CommonPurePattern level)
    -> EvaluationWrapper level
evaluateApplication
    conditionEvaluator
    functionEvaluator
    symbolIdToEvaluator
    conditionSort
    childrenCondition
    app @ Application
        { applicationSymbolOrAlias = SymbolOrAlias
            -- TODO: Also use the symbolOrAliasParams.
            { symbolOrAliasConstructor = symbolId }
        }
  = trace "evaluate-application" $
    EvaluationWrapper $
        case Map.lookup symbolId symbolIdToEvaluator of
            Nothing -> return unchanged
            Just evaluators -> do
                results <- mapM (applyEvaluator app) evaluators
                mergedResults <-
                    mapM (mergeWithCondition conditionEvaluator conditionSort childrenCondition) results
                -- TODO: nub is O(n^2), should do better than that
                trace (show results) $ case nub (filter notNotApplicable mergedResults) of
                    [] -> return unchanged
                    [NotApplicable] -> error "Should not reach this line."
                    [Symbolic condition] ->
                        return FunctionResult
                            { functionResultPattern =
                                asPurePattern $ ApplicationPattern app
                            , functionResultCondition = condition
                            }
                    [Applied functionResult] -> trace ("evaluate-application " ++ show functionResult) $ return functionResult
                    (_ : _ : _) -> error "Not implemented yet."
  where
    unchanged = FunctionResult
        { functionResultPattern   = asPurePattern $ ApplicationPattern app
        , functionResultCondition = childrenCondition
        }
    applyEvaluator app' (ApplicationFunctionEvaluator evaluator) =
        evaluator
            conditionEvaluator
            functionEvaluator
            app'
    notNotApplicable =
        \case
            NotApplicable -> False
            _ -> True

mergeWithCondition
    :: ConditionEvaluator level
    -> Sort level
    -> EvaluatedCondition level
    -> FunctionEvaluation level
    -> IntCounter (FunctionEvaluation level)
mergeWithCondition _ _ _ NotApplicable = return NotApplicable
mergeWithCondition conditionEvaluator conditionSort toMerge (Symbolic condition)
  = trace ("mergeWithCondition - Symbolic: " ++ show toMerge) $ do
    mergedCondition <-
        mergeConditions conditionEvaluator conditionSort condition toMerge
    case mergedCondition of
        ConditionFalse -> return NotApplicable
        _              -> return $ Symbolic mergedCondition
mergeWithCondition
    conditionEvaluator
    conditionSort
    toMerge
    (Applied functionResult)
  = multiTrace ["mergeWithCondition - Applied: ", "  " ++ show toMerge, "  "  ++ show (functionResultCondition functionResult), "  "  ++ show (functionResultPattern functionResult)] $ do
    mergedCondition <-
        mergeConditions
            conditionEvaluator
            conditionSort
            (functionResultCondition functionResult)
            toMerge
    case mergedCondition of
        ConditionFalse -> return NotApplicable
        _ -> trace ("mergeWithCondition - Applied: " ++ show mergedCondition) $ return $
            Applied functionResult {functionResultCondition = mergedCondition}

mergeConditions
    :: ConditionEvaluator level
    -> Sort level
    -> EvaluatedCondition level
    -> EvaluatedCondition level
    -> IntCounter (EvaluatedCondition level)
mergeConditions _ conditionSort first second =
    return $ makeEvaluatedAnd conditionSort first second
    -- TODO: Should be something like:
    -- conditionEvaluator (makeEvaluatedAnd conditionSort first second)
    -- but, right now, we don't have conditions which are partly satisfiable.
