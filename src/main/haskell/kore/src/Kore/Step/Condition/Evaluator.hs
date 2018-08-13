{-|
Module      : Kore.Step.Condition.Evaluator
Description : Evaluates conditions.
Copyright   : (c) Runtime Verification, 2018
License     : UIUC/NCSA
Maintainer  : virgil.serbanuta@runtimeverification.com
Stability   : experimental
Portability : portable
-}
module Kore.Step.Condition.Evaluator
    ( evaluateFunctionCondition
    ) where

import Data.List
       ( foldl' )
import Data.Reflection
       ( Given )

import Kore.AST.Common
       ( And (..), Equals (..), Iff (..), Implies (..), Not (..), Or (..),
       Pattern (..), SortedVariable )
import Kore.AST.MetaOrObject
import Kore.AST.PureML
       ( PureMLPattern, asPurePattern, fromPurePattern )
import Kore.IndexedModule.MetadataTools
       ( SortTools )
import Kore.Predicate.Predicate
       ( Predicate, PredicateProof (..), makeAndPredicate, makeEqualsPredicate,
       makeFalsePredicate, makeIffPredicate, makeImpliesPredicate,
       makeNotPredicate, makeOrPredicate, makeTruePredicate, unwrapPredicate,
       wrapPredicate )
import Kore.Step.ExpandedPattern
       ( ExpandedPattern (..), substitutionToPredicate )
import Kore.Step.Function.Data
       ( PureMLPatternFunctionEvaluator (..) )
import Kore.Variables.Fresh.IntCounter
       ( IntCounter )

{-| 'evaluateFunctionCondition' attempts to evaluate a Kore condition.

Right now the evaluation is rather rudimentary and gives up failry easy,
returning 'ConditionUnevaluable'.
-}
evaluateFunctionCondition
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable variable
        , Show (variable level)
        , Eq (variable level))
    => PureMLPatternFunctionEvaluator level variable
    -- ^ Evaluates functions in a pattern.
    -> Predicate level variable
    -- ^ The condition to be evaluated.
    -- TODO: Can't it happen that I also get a substitution when evaluating
    -- functions? See the Equals case.
    -> IntCounter (Predicate level variable, PredicateProof level)
evaluateFunctionCondition
    functionEvaluator
    predicate'
  =
    evaluateFunctionConditionInternal
        functionEvaluator
        (fromPurePattern (unwrapPredicate predicate'))

{-| 'evaluateFunctionCondition' attempts to evaluate a Kore condition.

Right now the evaluation is rather rudimentary and gives up failry easy,
returning 'ConditionUnevaluable'.
-}
evaluateFunctionConditionInternal
    ::  ( MetaOrObject level
        , Given (SortTools level)
        , SortedVariable variable
        , Show (variable level)
        , Eq (variable level))
    => PureMLPatternFunctionEvaluator level variable
    -> Pattern level variable (PureMLPattern level variable)
    -> IntCounter (Predicate level variable, PredicateProof level)
evaluateFunctionConditionInternal
    functionEvaluator
    (AndPattern And {andFirst = first, andSecond = second})
  = do
    (a, _) <- evaluateFunctionConditionInternal
        functionEvaluator (fromPurePattern first)
    (b, _) <- evaluateFunctionConditionInternal
        functionEvaluator (fromPurePattern second)
    return $ makeAndPredicate a b
evaluateFunctionConditionInternal
    functionEvaluator
    (OrPattern Or {orFirst = first, orSecond = second})
  = do
    (a, _) <- evaluateFunctionConditionInternal
        functionEvaluator (fromPurePattern first)
    (b, _) <- evaluateFunctionConditionInternal
        functionEvaluator (fromPurePattern second)
    return $ makeOrPredicate a b
evaluateFunctionConditionInternal
    functionEvaluator
    (NotPattern Not {notChild = patt})
  = do
    (a, _) <- evaluateFunctionConditionInternal
        functionEvaluator (fromPurePattern patt)
    return (makeNotPredicate a)
evaluateFunctionConditionInternal
    functionEvaluator
    (ImpliesPattern Implies {impliesFirst = first, impliesSecond = second})
  = do
    (a, _) <- evaluateFunctionConditionInternal
        functionEvaluator (fromPurePattern first)
    (b, _) <- evaluateFunctionConditionInternal
        functionEvaluator (fromPurePattern second)
    return $ makeImpliesPredicate a b
evaluateFunctionConditionInternal
    functionEvaluator
    (IffPattern Iff {iffFirst = first, iffSecond = second})
  = do
    (a, _) <- evaluateFunctionConditionInternal
        functionEvaluator (fromPurePattern first)
    (b, _) <- evaluateFunctionConditionInternal
        functionEvaluator (fromPurePattern second)
    return $ makeIffPredicate a b
evaluateFunctionConditionInternal
    (PureMLPatternFunctionEvaluator functionEvaluator)
    (EqualsPattern Equals {equalsFirst = first, equalsSecond = second})
  = do
    firstValue <- functionEvaluator first
    secondValue <- functionEvaluator second
    let
        (   ExpandedPattern
                { term = firstTerm
                , predicate = firstPredicate
                , substitution = firstSubstitution
                }
            , _
            ) = firstValue
        (   ExpandedPattern
                { term   = secondTerm
                , predicate = secondPredicate
                , substitution = secondSubstitution
                }
            , _
            ) = secondValue
        (mergedNewConditions, _) =
            foldl'
                (\(p1, _) p2 -> makeAndPredicate p1 p2)
                (makeTruePredicate, PredicateProof)
                [ firstPredicate
                , secondPredicate
                -- TODO(virgil): I should return the substitution.
                , substitutionToPredicate firstSubstitution
                , substitutionToPredicate secondSubstitution
                ]
    -- TODO(virgil): I should not try to evaluate `variable=pattern`.
    if firstTerm == secondTerm
        -- TODO(virgil): this should probably call evaluateFunctionCondition
        then return (mergedNewConditions, PredicateProof)
        else return $
            makeAndPredicate
                (makeEqualsPredicate firstTerm secondTerm)
                mergedNewConditions
evaluateFunctionConditionInternal
    _ (TopPattern _)
  = return (makeTruePredicate, PredicateProof)
evaluateFunctionConditionInternal
    _ (BottomPattern _)
  = return (makeFalsePredicate, PredicateProof)
evaluateFunctionConditionInternal
    _ patt
  = return (wrapPredicate (asPurePattern patt), PredicateProof)
