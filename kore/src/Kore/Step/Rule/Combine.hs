{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Step.Rule.Combine
    ( mergeRules
    , mergeRulesPredicate
    ) where

import Control.Applicative
    ( empty
    )
import Data.Default
    ( Default (..)
    )
import qualified Data.Foldable as Foldable
import qualified Data.List as List
import Data.List.NonEmpty
    ( NonEmpty ((:|))
    )
import Data.Set
    ( Set
    )
import qualified Data.Set as Set

import qualified Branch as BranchT
import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (FreeVariables)
    )
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional.DoNotUse
import qualified Kore.Internal.Predicate as Predicate
    ( fromPredicate
    )
import Kore.Internal.TermLike
    ( mkAnd
    )
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.Predicate.Predicate
    ( makeAndPredicate
    , makeCeilPredicate
    , makeMultipleAndPredicate
    , makeTruePredicate
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import Kore.Step.Rule
    ( RewriteRule (RewriteRule)
    , RulePattern (RulePattern)
    , refreshRulePattern
    )
import qualified Kore.Step.Rule as RulePattern
    ( applySubstitution
    , freeVariables
    )
import qualified Kore.Step.Rule as Rule.DoNotUse
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , SimplifierVariable
    , simplifyPredicate
    )
import qualified Kore.Step.SMT.Evaluator as SMT
    ( evaluate
    )
import Kore.Substitute
    ( SubstitutionVariable
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )

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
mergeRulesPredicate
    :: SubstitutionVariable variable
    => [RewriteRule variable]
    -> Syntax.Predicate variable
mergeRulesPredicate rules =
    mergeDisjointVarRulesPredicate
    $ renameRulesVariables rules

mergeDisjointVarRulesPredicate
    :: SubstitutionVariable variable
    => [RewriteRule variable]
    -> Syntax.Predicate variable
mergeDisjointVarRulesPredicate rules =
    makeMultipleAndPredicate
    $ map mergeRulePairPredicate
    $ makeConsecutivePairs rules

makeConsecutivePairs :: [a] -> [(a, a)]
makeConsecutivePairs [] = []
makeConsecutivePairs [_] = []
makeConsecutivePairs (a1 : a2 : as) = (a1, a2) : makeConsecutivePairs (a2 : as)

mergeRulePairPredicate
    :: InternalVariable variable
    => (RewriteRule variable, RewriteRule variable)
    -> Syntax.Predicate variable
mergeRulePairPredicate
    ( RewriteRule RulePattern {right = right1, ensures = ensures1}
    , RewriteRule RulePattern
        {left = left2, requires = requires2, antiLeft = Nothing}
    )
  =
    makeMultipleAndPredicate
        [ makeCeilPredicate (mkAnd right1 left2)
        , ensures1
        , requires2
        ]
mergeRulePairPredicate
    ( _
    , RewriteRule RulePattern {antiLeft = Just _}
    )
  =
    error "AntiLeft(priority-based rules) not handled when merging yet."

renameRulesVariables
    :: SubstitutionVariable variable
    => [RewriteRule variable]
    -> [RewriteRule variable]
renameRulesVariables
    = List.reverse . snd . List.foldl' renameRuleVariable (Set.empty, [])

renameRuleVariable
    :: SubstitutionVariable variable
    => (Set (UnifiedVariable variable), [RewriteRule variable])
    -> RewriteRule variable
    -> (Set (UnifiedVariable variable), [RewriteRule variable])
renameRuleVariable
    (usedVariables, processedRules)
    (RewriteRule rulePattern)
  = (newUsedVariables, RewriteRule newRulePattern : processedRules)
  where
    newUsedVariables =
        usedVariables
        `Set.union` ruleVariables
        `Set.union` newRuleVariables

    (FreeVariables ruleVariables) = RulePattern.freeVariables rulePattern

    (FreeVariables newRuleVariables) = RulePattern.freeVariables rulePattern

    (_, newRulePattern) =
        refreshRulePattern (FreeVariables usedVariables) rulePattern

mergeRules
    :: (MonadSimplify simplifier, SimplifierVariable variable)
    => NonEmpty (RewriteRule variable)
    -> simplifier [RewriteRule variable]
mergeRules (a :| []) = return [a]
mergeRules (renameRulesVariables . Foldable.toList -> rules) =
    BranchT.gather $ do
        Conditional {term = (), predicate, substitution} <-
            simplifyPredicate . Predicate.fromPredicate
            $ makeAndPredicate firstRequires mergedPredicate
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
                        , right = lastRight
                        , ensures = lastEnsures
                        , attributes = def
                        }

        return (RewriteRule finalRule)
  where
    mergedPredicate = mergeRulesPredicate rules
    firstRule = head rules
    RewriteRule RulePattern
        {left = firstLeft, requires = firstRequires, antiLeft = firstAntiLeft}
      =
        firstRule
    RewriteRule RulePattern {right = lastRight, ensures = lastEnsures} =
        last rules
