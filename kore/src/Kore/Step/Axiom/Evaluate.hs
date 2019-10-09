{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Step.Axiom.Evaluate
    ( evaluateAxioms
    ) where

import qualified Control.Monad as Monad
import Control.Monad.Trans.Maybe
    ( runMaybeT
    )
import qualified Data.Foldable as Foldable
import Data.Function
import Data.Maybe
    ( fromMaybe
    )
import Data.Sequence as Seq
    ( zipWith
    )

import qualified Kore.Attribute.Axiom as Attribute.Axiom
import qualified Kore.Attribute.Axiom.Concrete as Attribute.Axiom.Concrete
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import qualified Kore.Internal.Predicate as Predicate
import Kore.Internal.TermLike
    ( TermLike
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
    , StepContext (..)
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
import qualified Kore.Unification.Unify as Monad.Unify
import Kore.Variables.Fresh
import Kore.Variables.Target
    ( Target (..)
    )

evaluateAxioms
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => StepContext
    -> [EqualityRule Variable]
    -> TermLike variable
    -> Syntax.Predicate variable
    -> simplifier (AttemptedAxiom variable)
evaluateAxioms a b c d = resultsToAttemptedAxiom <$> evaluateAxioms' a b c d
-- ^ TODO (andrei.burdusa): remove this

evaluateAxioms'
    :: forall variable simplifier
    .  (SimplifierVariable variable, MonadSimplify simplifier)
    => StepContext
    -> [EqualityRule Variable]
    -> TermLike variable
    -> Syntax.Predicate variable
    -> simplifier (Result.Results (Step.UnifiedRule (Target variable)) (Pattern variable))
evaluateAxioms'
    context
    definitionRules
    patt
    predicate
  | any ruleIsConcrete definitionRules
  , not (TermLike.isConcrete patt)
  = return $ Result.Results mempty mempty
  | otherwise
  = maybeResults $ do
    let
        -- TODO (thomas.tuegel): Figure out how to get the initial conditions
        -- and apply them here, to remove remainder branches sooner.
        expanded :: Pattern variable
        expanded = Pattern.fromTermLike patt

    results <- applyRules expanded (map unwrapEqualityRule definitionRules)
    Monad.guard (any Result.hasResults results)
    mapM_ rejectNarrowing results

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
        rules = Result.appliedRule <$> Result.results result

    simplifiedResults <-
        traverse (OrPattern.simplifyPredicatesWithSmt predicate)
            ((fmap Result.result . Result.results) result)

    simplifiedRemainders <-
        OrPattern.simplifyPredicatesWithSmt
            predicate (Step.remainders result)

    let
        returnedResults = zipResult rules simplifiedResults

    Monad.guard $ (not . Foldable.null . Foldable.fold . fmap Result.result) returnedResults

    return Result.Results
            { results = returnedResults
            , remainders = simplifiedRemainders
            }

  where
    maybeResults = fmap (fromMaybe (Result.Results mempty mempty)) . runMaybeT

    zipResult = Seq.zipWith Result.Result

    ruleIsConcrete =
        Attribute.Axiom.Concrete.isConcrete
        . Attribute.Axiom.concrete
        . RulePattern.attributes
        . getEqualityRule

    unwrapEqualityRule (EqualityRule rule) =
        RulePattern.mapVariables fromVariable rule

    rejectNarrowing (Result.results -> results) =
        (Monad.guard . not) (Foldable.any Step.isNarrowingResult results)

    applyRules
        (Step.toConfigurationVariables -> initial)
        rules
      = Monad.Unify.maybeUnifierT
        $ Step.checkFunctionLikeResults context initial
        $ Step.applyRulesSequence unificationProcedure initial rules

    ignoreUnificationErrors unification pattern1 pattern2 =
        Monad.Unify.runUnifierT (unification pattern1 pattern2)
        >>= either (couldNotMatch pattern1 pattern2) Monad.Unify.scatter

    couldNotMatch pattern1 pattern2 _ =
        Monad.Unify.explainAndReturnBottom
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
