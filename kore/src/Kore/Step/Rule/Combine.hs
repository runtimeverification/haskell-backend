{- |
Copyright   : (c) Runtime Verification, 2019
License     : BSD-3-Clause
-}
module Kore.Step.Rule.Combine (
    mergeRules,
    mergeRulesConsecutiveBatches,
    mergeRulesPredicate,
    renameRulesVariables,
) where

import Control.Monad.State.Strict (
    State,
    evalState,
 )
import qualified Control.Monad.State.Strict as State
import Data.Default (
    Default (..),
 )
import Kore.Attribute.Pattern.FreeVariables (
    FreeVariables,
    freeVariables,
 )
import qualified Kore.Internal.Condition as Condition (
    fromPredicate,
 )
import Kore.Internal.Conditional (
    Conditional (Conditional),
 )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
import Kore.Internal.Predicate (
    Predicate,
    makeAndPredicate,
    makeCeilPredicate,
    makeMultipleAndPredicate,
    makeNotPredicate,
    makeTruePredicate,
 )
import qualified Kore.Internal.SideCondition as SideCondition (
    topTODO,
 )
import Kore.Internal.TermLike (
    mkAnd,
 )
import Kore.Internal.Variable (
    InternalVariable,
 )
import Kore.Rewriting.RewritingVariable (
    RewritingVariableName,
 )
import qualified Kore.Step.AntiLeft as AntiLeft (
    antiLeftPredicate,
 )
import Kore.Step.RulePattern (
    RHS (RHS),
    RewriteRule (RewriteRule),
    RulePattern (RulePattern),
 )
import qualified Kore.Step.RulePattern as Rule.DoNotUse
import qualified Kore.Step.RulePattern as RulePattern (
    applySubstitution,
 )
import qualified Kore.Step.SMT.Evaluator as SMT (
    evaluate,
 )
import Kore.Step.Simplification.Simplify (
    MonadSimplify,
    simplifyCondition,
 )
import Kore.Step.Step (
    refreshRule,
 )
import qualified Logic
import Prelude.Kore

{-
Given a list of rules

@
L1 -> R1
L2 -> R2
...
Ln -> Rn
@

returns a predicate P such that applying the above rules in succession
is the same as applying @(L1 and P) => Rn@.

See docs/2019-09-09-Combining-Rewrite-Axioms.md for details.
-}
mergeRulesPredicate ::
    InternalVariable variable =>
    [RewriteRule variable] ->
    Predicate variable
mergeRulesPredicate rules =
    mergeDisjointVarRulesPredicate $
        renameRulesVariables rules

mergeDisjointVarRulesPredicate ::
    InternalVariable variable =>
    [RewriteRule variable] ->
    Predicate variable
mergeDisjointVarRulesPredicate rules =
    makeMultipleAndPredicate $
        map mergeRulePairPredicate $
            makeConsecutivePairs rules

makeConsecutivePairs :: [a] -> [(a, a)]
makeConsecutivePairs [] = []
makeConsecutivePairs [_] = []
makeConsecutivePairs (a1 : a2 : as) = (a1, a2) : makeConsecutivePairs (a2 : as)

mergeRulePairPredicate ::
    InternalVariable variable =>
    (RewriteRule variable, RewriteRule variable) ->
    Predicate variable
mergeRulePairPredicate
    ( RewriteRule RulePattern{rhs = RHS{right = right1, ensures = ensures1}}
        , RewriteRule
            RulePattern
                { left = left2
                , requires = requires2
                , antiLeft = antiLeft2
                }
        ) =
        makeMultipleAndPredicate
            [ makeCeilPredicate (mkAnd right1 left2)
            , ensures1
            , requires2
            , antiLeftPredicate
            ]
      where
        antiLeftPredicate = case antiLeft2 of
            Nothing -> makeTruePredicate
            Just antiLeft ->
                makeNotPredicate $ AntiLeft.antiLeftPredicate antiLeft right1

renameRulesVariables ::
    forall variable.
    InternalVariable variable =>
    [RewriteRule variable] ->
    [RewriteRule variable]
renameRulesVariables rules =
    evalState (traverse renameRule rules) mempty
  where
    renameRule ::
        RewriteRule variable ->
        State (FreeVariables variable) (RewriteRule variable)
    renameRule rewriteRule = State.state $ \used ->
        let (_, rewriteRule') = refreshRule used rewriteRule
         in (rewriteRule', used <> freeVariables rewriteRule')

mergeRules ::
    MonadSimplify simplifier =>
    NonEmpty (RewriteRule RewritingVariableName) ->
    simplifier [RewriteRule RewritingVariableName]
mergeRules (a :| []) = return [a]
mergeRules (renameRulesVariables . toList -> rules) =
    Logic.observeAllT $ do
        Conditional{term = (), predicate, substitution} <-
            simplifyCondition SideCondition.topTODO . Condition.fromPredicate $
                makeAndPredicate firstRequires mergedPredicate
        evaluation <- SMT.evaluate predicate
        evaluatedPredicate <- case evaluation of
            Nothing -> return predicate
            Just True -> return makeTruePredicate
            Just False -> empty

        let finalRule =
                RulePattern.applySubstitution
                    substitution
                    RulePattern
                        { left = firstLeft
                        , requires = evaluatedPredicate
                        , antiLeft = firstAntiLeft
                        , rhs = lastRHS
                        , attributes = def
                        }

        return (RewriteRule finalRule)
  where
    mergedPredicate = mergeDisjointVarRulesPredicate rules
    firstRule = head rules
    RewriteRule
        RulePattern
            { left = firstLeft
            , requires = firstRequires
            , antiLeft = firstAntiLeft
            } =
            firstRule
    RewriteRule RulePattern{rhs = lastRHS} =
        last rules

{- | Merge rules in consecutive batches.

As an example, when trying to merge rules 1..9 in batches of 4, it
first merges rules 1, 2, 3 and 4 into rule 4', then rules 4', 5, 6, 7
into rule 7', then returns the result of merging 7', 8 and 9.
-}
mergeRulesConsecutiveBatches ::
    MonadSimplify simplifier =>
    -- | Batch size
    Int ->
    NonEmpty (RewriteRule RewritingVariableName) ->
    -- Rules to merge
    simplifier [RewriteRule RewritingVariableName]
mergeRulesConsecutiveBatches
    batchSize
    (rule :| rules)
        | batchSize <= 1 = error ("Invalid group size: " ++ show batchSize)
        | null rules = return [rule]
        | otherwise = do
            let (rulesBatch, remainder) = splitAt (batchSize - 1) rules
            mergedRulesList <- mergeRules (rule :| rulesBatch)
            Logic.observeAllT $ do
                mergedRule <- Logic.scatter mergedRulesList
                allMerged <-
                    mergeRulesConsecutiveBatches batchSize (mergedRule :| remainder)
                Logic.scatter allMerged
