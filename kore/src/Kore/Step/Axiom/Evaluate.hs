{- |
Copyright   : (c) Runtime Verification, 2019
License     : NCSA

-}
module Kore.Step.Axiom.Evaluate
    ( evaluateAxioms
    ) where

import Prelude.Kore

import qualified Control.Comonad.Trans.Cofree as Cofree
import Control.Error
    ( maybeT
    )
import Control.Lens.Combinators as Lens
import qualified Control.Monad as Monad
import qualified Data.Functor.Foldable as Recursive
import Data.Generics.Product

import qualified Kore.Attribute.Axiom as Attribute.Axiom
import qualified Kore.Attribute.Axiom as Attribute
    ( Axiom (Axiom)
    )
import qualified Kore.Attribute.Axiom.Concrete as Attribute.Axiom.Concrete
import qualified Kore.Internal.OrPattern as OrPattern
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
import Kore.Internal.SideCondition
    ( SideCondition
    )
import Kore.Internal.TermLike
    ( TermLike
    , mkEvaluated
    )
import qualified Kore.Internal.TermLike as TermLike
import qualified Kore.Log.DebugAxiomEvaluation as DebugAxiomEvaluation
    ( attemptAxiom
    , klabelIdentifier
    )
import Kore.Step.Axiom.Identifier
    ( matchAxiomIdentifier
    )
import Kore.Step.EqualityPattern
    ( EqualityPattern (EqualityPattern)
    , EqualityRule (..)
    )
import qualified Kore.Step.EqualityPattern as EqualityPattern
    ( EqualityPattern (..)
    )
import qualified Kore.Step.EquationalStep as Step
import Kore.Step.Remainder
    ( ceilChildOfApplicationOrTop
    )
import qualified Kore.Step.Result as Result
import qualified Kore.Step.Simplification.OrPattern as OrPattern
import Kore.Step.Simplification.Simplify
    ( InternalVariable
    , MonadSimplify
    )
import qualified Kore.Step.Step as EqualityPattern
    ( mapRuleVariables
    )
import qualified Kore.Unification.UnifierT as Unifier
import Kore.Variables.Fresh
import Log
    ( MonadLog
    )

evaluateAxioms
    :: forall variable simplifier
    .  ( InternalVariable variable
       , MonadSimplify simplifier
       )
    => [EqualityRule Variable]
    -> SideCondition variable
    -> TermLike variable
    -> simplifier (Step.Results EqualityPattern variable)
evaluateAxioms equalityRules sideCondition termLike
  | any ruleIsConcrete equalityRules
  -- All of the current pattern's children (most likely an ApplicationF)
  -- must be ConstructorLike in order to be evaluated with "concrete" rules.
  , not (all TermLike.isConstructorLike termLikeF)
  = return notApplicable
  | otherwise
  = maybeNotApplicable $ do
    let
        expanded :: Pattern variable
        expanded = Pattern.fromTermLike termLike

    -- TODO (virgil): Consider logging the rules in Step.unifyRules or some
    -- similar place, especially if we start logging unification details.
    mapM_ logAppliedRule equalityRules
    resultss <- applyRules expanded (map unwrapEqualityRule equalityRules)
    Monad.guard (any Result.hasResults resultss)
    mapM_ rejectNarrowing resultss

    ceilChild <- ceilChildOfApplicationOrTop sideCondition termLike
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

    let simplify = OrPattern.simplifyConditionsWithSmt sideCondition
    simplified <-
        return results
        >>= Lens.traverseOf
            (field @"results" . Lens.traversed . field @"result")
            simplify
        >>= Lens.traverseOf (field @"remainders") simplify
    -- This guard is wrong: It leaves us unable to distinguish between a
    -- not-applicable result and a Bottom result. This check should be handled
    -- in Kore.Step.Step, but the initial condition is not available there.
    Monad.guard (any (not . null) $ Result.results simplified)
    return simplified

  where
    termLikeF = Cofree.tailF (Recursive.project termLike)

    targetSideCondition = Step.toConfigurationVariablesCondition sideCondition

    logAppliedRule :: MonadLog log => EqualityRule Variable -> log ()
    logAppliedRule
        (EqualityRule EqualityPattern
            {left, attributes = Attribute.Axiom {sourceLocation}}
        )
      =
        DebugAxiomEvaluation.attemptAxiom
            sourceLocation
            (matchAxiomIdentifier left)
            (DebugAxiomEvaluation.klabelIdentifier left)

    ruleIsConcrete =
        Attribute.Axiom.Concrete.isConcrete
        . Attribute.Axiom.concrete
        . EqualityPattern.attributes
        . getEqualityRule

    notApplicable =
        Result.Results
            { results = mempty
            , remainders = OrPattern.fromTermLike $ mkEvaluated termLike
            }

    maybeNotApplicable = maybeT (return notApplicable) return

    unwrapEqualityRule (EqualityRule rule) =
        EqualityPattern.mapRuleVariables
            (fmap fromVariable)
            (fmap fromVariable)
            rule

    rejectNarrowing (Result.results -> results) =
        (Monad.guard . not) (any Step.isNarrowingResult results)

    applyRules (Step.toConfigurationVariables -> initial) rules =
        Unifier.maybeUnifierT
        $ Step.applyRulesSequence
            targetSideCondition
            initial
            rules
