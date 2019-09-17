{-|
Copyright   : (c) Runtime Verification, 2019
License     : NCSA
-}

module Kore.Step.Rule.Combine
    ( mergeRulesPredicate
    ) where

import qualified Data.List as List
import Data.Set
    ( Set
    )
import qualified Data.Set as Set

import Kore.Attribute.Pattern.FreeVariables
    ( FreeVariables (FreeVariables)
    )
import Kore.Internal.TermLike
    ( mkAnd
    )
import Kore.Internal.Variable
    ( InternalVariable
    )
import Kore.Predicate.Predicate
    ( makeCeilPredicate
    , makeMultipleAndPredicate
    )
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import Kore.Step.Rule
    ( RewriteRule (RewriteRule)
    , RulePattern (RulePattern)
    , refreshRulePattern
    )
import qualified Kore.Step.Rule as Rule
    ( freeVariables
    )
import qualified Kore.Step.Rule as Rule.DoNotUse
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
    makeMultipleAndPredicate
    $ map mergeRulePairPredicate
    $ makeConsecutivePairs
    $ renameRulesVariables rules

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
    , RewriteRule RulePattern {left = left2, requires = requires2}
    )
  =
    makeMultipleAndPredicate
        [ makeCeilPredicate (mkAnd right1 left2)
        , ensures1
        , requires2
        ]

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

    (FreeVariables ruleVariables) = Rule.freeVariables rulePattern

    (FreeVariables newRuleVariables) = Rule.freeVariables rulePattern

    (_, newRulePattern) =
        refreshRulePattern (FreeVariables usedVariables) rulePattern
