{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Step.Axiom.Evaluate
    ( evaluateAxioms
    , resultsToAttemptedAxiom
    ) where

import Control.Lens.Combinators as Lens
import qualified Data.Foldable as Foldable
import Data.Function
import Data.Generics.Product

import qualified Kore.Attribute.Axiom as Attribute.Axiom
import qualified Kore.Attribute.Axiom.Concrete as Attribute.Axiom.Concrete
import Kore.Internal.MultiOr
    ( MultiOr (..)
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
    ( TermLike
    , mkEvaluated
    )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Predicate.Predicate as Syntax
    ( Predicate
    )
import Kore.Step.Axiom.Matcher
    ( matchIncremental
    )
import Kore.Step.Remainder
    ( ceilChildOfApplicationOrTop
    )
import qualified Kore.Step.Result as Result
import Kore.Step.Rule
    ( EqualityRule (..)
    )
import qualified Kore.Step.Rule as RulePattern
    ( RulePattern (..)
    , mapVariables
    )
import qualified Kore.Step.Simplification.OrPattern as OrPattern
import Kore.Step.Simplification.Simplify
    ( AttemptedAxiom (..)
    , AttemptedAxiomResults (..)
    , MonadSimplify
    , SimplifierVariable
    )
import Kore.Step.Step
    ( UnificationProcedure (..)
    )
import qualified Kore.Step.Step as Step
import qualified Kore.Unification.UnifierT as Unifier
import Kore.Variables.Fresh

evaluateAxioms
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => [EqualityRule Variable]
    -> TermLike variable
    -> Syntax.Predicate variable
    -> simplifier (Step.Results variable)
evaluateAxioms
    definitionRules
    patt
    predicate
  | any ruleIsConcrete definitionRules
  , not (TermLike.isConcrete patt)
  = return mempty
  | otherwise
  = do
    let
        -- TODO (thomas.tuegel): Figure out how to get the initial conditions
        -- and apply them here, to remove remainder branches sooner.
        expanded, evaluated :: Pattern variable
        expanded = Pattern.fromTermLike patt

        evaluated = Pattern.fromTermLike $ mkEvaluated patt

    eitherResults <- applyRules expanded (map unwrapEqualityRule definitionRules)

    case eitherResults of
        Left _ -> return Result.Results
                        { results = mempty, remainders = MultiOr [evaluated] }
        Right results
          | any (any Step.isNarrowingResult . Result.results) results ->
            return Result.Results
                { results = mempty, remainders = MultiOr [evaluated] }
          | (not . any Result.hasResults) results ->
            return Result.Results
                { results = mempty, remainders = MultiOr [evaluated] }
          | otherwise -> do
            ceilChild <- ceilChildOfApplicationOrTop Predicate.topTODO patt
            let
                result =
                    Result.mergeResults results
                    & Result.mapConfigs
                        keepResultUnchanged
                        ( markRemainderEvaluated
                        . introduceDefinedness ceilChild
                        )
                keepResultUnchanged = id
                introduceDefinedness = flip Pattern.andCondition
                markRemainderEvaluated = fmap TermLike.mkEvaluated

            simplifiedResult <-
                Lens.traverseOf
                    (field @"results" . Lens.traversed . field @"result")
                    (OrPattern.simplifyPredicatesWithSmt predicate)
                    result
                    >>= Lens.traverseOf (field @"remainders")
                        (OrPattern.simplifyPredicatesWithSmt predicate)

            let Result.Results { results = returnedResults } = simplifiedResult

            if (all null . fmap Result.result) returnedResults
                then return Result.Results
                    { results = mempty, remainders = MultiOr [evaluated] }
                else return simplifiedResult

  where
    ruleIsConcrete =
        Attribute.Axiom.Concrete.isConcrete
        . Attribute.Axiom.concrete
        . RulePattern.attributes
        . getEqualityRule

    unwrapEqualityRule (EqualityRule rule) =
        RulePattern.mapVariables fromVariable rule

    applyRules (Step.toConfigurationVariables -> initial) rules
      = Unifier.runUnifierT
        $ Step.applyRulesSequence unificationProcedure initial rules

    ignoreUnificationErrors unification pattern1 pattern2 =
        Unifier.runUnifierT (unification pattern1 pattern2)
        >>= either (couldNotMatch pattern1 pattern2) Unifier.scatter

    couldNotMatch pattern1 pattern2 _ =
        Unifier.explainAndReturnBottom
            "Could not match patterns"
            pattern1
            pattern2

    unificationProcedure =
        UnificationProcedure (ignoreUnificationErrors matchIncremental)

resultsToAttemptedAxiom
    :: (Ord variable)
    => Result.Results rule (Pattern variable)
    -> AttemptedAxiom variable
resultsToAttemptedAxiom
    (Result.Results results remainders)
  | null results'
    = NotApplicable
  | otherwise
    = Applied $ AttemptedAxiomResults results' remainders
  where
    results' = Foldable.fold $ fmap Result.result results
