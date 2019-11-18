{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Step.Axiom.Evaluate
    ( evaluateAxioms
    ) where

import Control.Error
    ( maybeT
    )
import Control.Lens.Combinators as Lens
import qualified Control.Monad as Monad
import Data.Function
import Data.Generics.Product

import qualified Kore.Attribute.Axiom as Attribute.Axiom
import qualified Kore.Attribute.Axiom.Concrete as Attribute.Axiom.Concrete
import qualified Kore.Internal.Condition as Condition
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.Predicate
    ( Predicate
    )
import Kore.Internal.TermLike
    ( TermLike
    , mkEvaluated
    )
import qualified Kore.Internal.TermLike as TermLike
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
    ( MonadSimplify
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
    .  ( SimplifierVariable variable
       , MonadSimplify simplifier
       )
    => [EqualityRule Variable]
    -> TermLike variable
    -> Predicate variable
    -> simplifier (Step.Results variable)
evaluateAxioms definitionRules termLike predicate
  | any ruleIsConcrete definitionRules
  , not (TermLike.isConcrete termLike)
  = return notApplicable
  | otherwise
  = maybeNotApplicable $ do
    let
        -- TODO (thomas.tuegel): Figure out how to get the initial conditions
        -- and apply them here, to remove remainder branches sooner.
        expanded :: Pattern variable
        expanded = Pattern.fromTermLike termLike

    resultss <- applyRules expanded (map unwrapEqualityRule definitionRules)
    Monad.guard (any Result.hasResults resultss)
    mapM_ rejectNarrowing resultss

    ceilChild <- ceilChildOfApplicationOrTop Condition.topTODO termLike
    let
        results =
            Result.mergeResults resultss
            & Result.mapConfigs
                keepResultUnchanged
                ( markRemainderEvaluated
                . introduceDefinedness ceilChild
                )
        keepResultUnchanged = id
        introduceDefinedness = flip Pattern.andCondition
        markRemainderEvaluated = fmap TermLike.mkEvaluated

    let simplify = OrPattern.simplifyConditionsWithSmt predicate
    simplified <-
        return results
        >>= Lens.traverseOf (field @"results" . Lens.traversed . field @"result") simplify
        >>= Lens.traverseOf (field @"remainders") simplify
    -- This guard is wrong: It leaves us unable to distinguish between a
    -- not-applicable result and a Bottom result. This check should be handled
    -- in Kore.Step.Step, but the initial condition is not available there.
    Monad.guard (any (not . null) $ Result.results simplified)
    return simplified

  where
    ruleIsConcrete =
        Attribute.Axiom.Concrete.isConcrete
        . Attribute.Axiom.concrete
        . RulePattern.attributes
        . getEqualityRule

    notApplicable =
        Result.Results
            { results = mempty
            , remainders = OrPattern.fromTermLike $ mkEvaluated termLike
            }

    maybeNotApplicable = maybeT (return notApplicable) return

    unwrapEqualityRule (EqualityRule rule) =
        RulePattern.mapVariables fromVariable rule

    rejectNarrowing (Result.results -> results) =
        (Monad.guard . not) (any Step.isNarrowingResult results)

    applyRules (Step.toConfigurationVariables -> initial) rules =
        Unifier.maybeUnifierT
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
