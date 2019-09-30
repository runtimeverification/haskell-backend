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
import qualified Control.Monad as Monad
import Data.Default
    ( Default (..)
    )
import qualified Data.List as List
import Data.List.NonEmpty
    ( NonEmpty ((:|))
    )
import qualified Data.List.NonEmpty as NonEmpty
    ( head
    , last
    , toList
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
import qualified Kore.Internal.TermLike as TermLike
    ( substitute
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
import qualified Kore.Predicate.Predicate as Syntax.Predicate
    ( substitute
    )
import Kore.Step.Rule
    ( RewriteRule (RewriteRule)
    , RulePattern (RulePattern)
    , refreshRulePattern
    )
import qualified Kore.Step.Rule as Rule
    ( freeVariables
    , isFreeOf
    )
import qualified Kore.Step.Rule as Rule.DoNotUse
import qualified Kore.Step.Simplification.Predicate as Predicate
import Kore.Step.Simplification.Simplify
    ( MonadSimplify
    , SimplifierVariable
    )
import qualified Kore.Step.SMT.Evaluator as SMT
    ( evaluate
    )
import Kore.Substitute
    ( SubstitutionVariable
    )
import qualified Kore.Unification.Substitution as Substitution
    ( toMap
    , variables
    )
import Kore.Variables.UnifiedVariable
    ( UnifiedVariable
    )

import Debug.Trace
import Kore.Unparser

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

    (FreeVariables ruleVariables) = Rule.freeVariables rulePattern

    (FreeVariables newRuleVariables) = Rule.freeVariables rulePattern

    (_, newRulePattern) =
        refreshRulePattern (FreeVariables usedVariables) rulePattern

mergeRules
    :: (MonadSimplify simplifier, SimplifierVariable variable)
    => NonEmpty (RewriteRule variable)
    -> simplifier [RewriteRule variable]
mergeRules (a :| []) = return [a]
mergeRules rules = BranchT.gather $ do
    traceM ("Initial: " ++ unparseToString mergedPredicate)
    Conditional {term = (), predicate, substitution} <-
        Predicate.simplify 0
            (Predicate.fromPredicate
                (makeAndPredicate firstRequires mergedPredicate)
            )
    traceM ("Simplified: " ++ unparseToString Conditional {term = (), predicate, substitution})
    evaluation <- SMT.evaluate predicate
    evaluatedPredicate <- case evaluation of
        Nothing -> return predicate
        Just True -> return makeTruePredicate
        Just False -> empty

    let subst = Substitution.toMap substitution
        finalLeft = TermLike.substitute subst firstLeft
        finalAntiLeft = TermLike.substitute subst <$> firstAntiLeft
        finalRight = TermLike.substitute subst lastRight
        finalEnsures = Syntax.Predicate.substitute subst lastEnsures
        finalRule = RulePattern
            { left = finalLeft
            , requires = evaluatedPredicate
            , antiLeft = finalAntiLeft
            , right = finalRight
            , ensures = finalEnsures
            , attributes = def
            }

        substitutedVariables = Substitution.variables substitution

    traceM ("right=" ++ unparseToString lastRight)
    traceM ("finalRight=" ++ unparseToString finalRight)
    Monad.unless (finalRule `Rule.isFreeOf` substitutedVariables)
        (error
            (  "Substituted variables not removed from the rule, cannot throw "
            ++ "substitution away."
            )
        )

    return (RewriteRule finalRule)
  where
    mergedPredicate = mergeRulesPredicate (NonEmpty.toList rules)
    firstRule = NonEmpty.head rules
    RewriteRule RulePattern
        {left = firstLeft, requires = firstRequires, antiLeft = firstAntiLeft}
      =
        firstRule
    RewriteRule RulePattern {right = lastRight, ensures = lastEnsures} =
        NonEmpty.last rules
