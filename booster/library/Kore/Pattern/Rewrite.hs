{- |
Copyright   : (c) Runtime Verification, 2022
License     : BSD-3-Clause
-}
module Kore.Pattern.Rewrite (
    rewriteStep,
    RewriteFailed (..),
    RuleFailed (..),
    RewriteResult (..),
) where

import Control.Monad
import Control.Monad.Trans.Except
import Data.Either
import Data.List.NonEmpty (NonEmpty (..))
import Data.List.NonEmpty qualified as NE
import Data.Map qualified as Map
import Data.Maybe (fromMaybe)

import Kore.Definition.Attributes.Base
import Kore.Definition.Base
import Kore.Pattern.Base
import Kore.Pattern.Simplify
import Kore.Pattern.Unify
import Kore.Pattern.Util

import Kore.Syntax.ParsedKore.Internalise (computeTermIndex) -- FIXME move this function!

{- | Performs a rewrite step (using suitable rewrite rules from the
   definition).

  The result can be a failure (providing some context for why it
  failed), or a rewritten pattern with a new term and possibly new
  additional constraints.
-}
rewriteStep :: KoreDefinition -> Pattern -> Except RewriteFailed RewriteResult
rewriteStep def pat = do
    let termIdx = computeTermIndex pat.term
    when (termIdx == None) $ throwE TermIndexIsNone

    let idxRules = fromMaybe Map.empty $ Map.lookup termIdx def.rewriteTheory
        anyRules = fromMaybe Map.empty $ Map.lookup Anything def.rewriteTheory
        rules = map snd . Map.toAscList $ Map.unionWith (<>) idxRules anyRules

    when (null rules) $ throwE NoRulesForTerm

    -- process one priority group at a time (descending priority),
    -- until a result is obtained or the entire rewrite fails.
    processGroups rules
  where
    processGroups :: [[RewriteRule]] -> Except RewriteFailed RewriteResult
    processGroups [] =
        throwE NoApplicableRules
    processGroups (rules : rest) = do
        -- try all rules of the priority group
        let (failures, results) =
                partitionEithers $ map (runExcept . applyRule def pat) rules

        -- if any rule failure is an uncertainty, fail the rewrite
        -- immediately
        let uncertains = filter isUncertain failures
        unless (null uncertains) $
            throwE $
                RuleApplicationUncertain uncertains

        -- if any of the results does not preserve definedness, fail
        -- the rewrite immediately
        let maybeUndefined =
                filter
                    (not . (.computedAttributes.preservesDefinedness) . fst)
                    results
        unless (null maybeUndefined) $
            throwE $
                DefinednessUnclear maybeUndefined

        -- simplify and filter out bottom states
        let finalResults = filter (not . isBottom) $ map (simplifyPattern . snd) results
        if null finalResults
            then processGroups rest
            else pure $ RewriteResult $ NE.fromList finalResults

{- | Tries to apply one rewrite rule:

 * Unifies the LHS term with the pattern term
 * Ensures that the unification is a _match_ (one-sided substitution)
 * prunes any rules that turn out to have trivially-false side conditions
 * returns the rule and the resulting pattern
-}
applyRule ::
    KoreDefinition ->
    Pattern ->
    RewriteRule ->
    Except RuleFailed (RewriteRule, Pattern)
applyRule def pat rule = do
    -- unify terms
    let unified = unifyTerms def rule.lhs.term pat.term
    subst <- case unified of
        UnificationFailed reason ->
            throwE $ RewriteUnificationFailed reason
        UnificationSortError sortError ->
            throwE $ RewriteSortError sortError
        UnificationRemainder remainder ->
            throwE $ RewriteUnificationUnclear rule remainder
        UnificationSuccess substitution ->
            pure substitution

    -- check it is a matching substitution (stop if not)
    unless (Map.keysSet subst == freeVariables rule.lhs.term) $
        throwE $
            UnificationIsNotMatch rule subst

    -- apply substitution to rule constraints and simplify (stop if
    -- false, one by one in isolation)
    let newConstraints =
            map (substituteInPredicate subst) $
                rule.lhs.constraints <> rule.rhs.constraints
    mapM_ checkConstraint newConstraints

    let rewritten =
            Pattern
                (substituteInTerm subst rule.rhs.term)
                (map (substituteInPredicate subst) $ pat.constraints <> newConstraints)
    return (rule, rewritten)
  where
    checkConstraint :: Predicate -> Except RuleFailed ()
    checkConstraint p =
        when (simplifyPredicate p == Bottom) $
            throwE $
                ConstraintIsBottom p

{- | Reason why a rewrite did not produce a result. Contains additional
   information for logging what happened during the rewrite.
-}
data RewriteFailed
    = -- | No rules have been found
      NoRulesForTerm
    | -- | All rules have been tried unsuccessfully
      NoApplicableRules
    | -- | It is uncertain whether or not rules can be applied
      RuleApplicationUncertain [RuleFailed]
    | -- | There are rewrites that do not preserve definedness
      DefinednessUnclear [(RewriteRule, Pattern)]
    | -- | Term has index 'None', no rule should apply
      TermIndexIsNone
    deriving stock (Eq, Show)

data RuleFailed
    = -- | The rule's LHS term and the pattern term do not unify at all
      RewriteUnificationFailed FailReason
    | -- | The rule's LHS term and the pattern term do not unify with certainty
      RewriteUnificationUnclear RewriteRule (NonEmpty (Term, Term))
    | -- | A sort error occurred during unification
      RewriteSortError SortError
    | -- | The unification did not produce a matching substitution
      UnificationIsNotMatch RewriteRule Substitution
    | -- | A constraint of the rule simplifies to Bottom (when substituted)
      ConstraintIsBottom Predicate
    deriving stock (Eq, Show)

isUncertain :: RuleFailed -> Bool
isUncertain RewriteUnificationFailed{} = False
isUncertain RewriteUnificationUnclear{} = True
isUncertain RewriteSortError{} = True
isUncertain UnificationIsNotMatch{} = True
isUncertain ConstraintIsBottom{} = False

newtype RewriteResult
    = RewriteResult (NonEmpty Pattern)
    deriving stock (Eq, Show)
    deriving newtype (Semigroup)
