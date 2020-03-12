{- |
Copyright   : (c) Runtime Verification, 2018
License     : NCSA

-}
module Kore.Step.Simplification.OrPattern
    ( simplifyConditionsWithSmt
    ) where

import Prelude.Kore

import Branch
    ( BranchT
    )
import qualified Branch as BranchT
import Kore.Internal.Condition
    ( Condition
    )
import qualified Kore.Internal.Condition as Condition
    ( bottom
    , fromPredicate
    , toPredicate
    )
import Kore.Internal.Conditional
    ( Conditional (Conditional)
    )
import qualified Kore.Internal.Conditional as Conditional
    ( Conditional (..)
    )
import qualified Kore.Internal.OrCondition as OrCondition
    ( gather
    )
import Kore.Internal.OrPattern
    ( OrPattern
    )
import qualified Kore.Internal.OrPattern as OrPattern
    ( gather
    )
import Kore.Internal.Pattern
    ( Pattern
    )
import qualified Kore.Internal.Pattern as Pattern
    ( splitTerm
    , withCondition
    )
import Kore.Internal.Predicate
    ( makeAndPredicate
    , makeNotPredicate
    , makeTruePredicate_
    )
import Kore.Internal.SideCondition
    ( SideCondition
    )
import qualified Kore.Internal.SideCondition as SideCondition
    ( toPredicate
    , top
    )
import Kore.Step.Simplification.Simplify
    ( InternalVariable
    , MonadSimplify
    , simplifyCondition
    )
import qualified Kore.Step.SMT.Evaluator as SMT.Evaluator
    ( filterMultiOr
    )
import Kore.TopBottom
    ( TopBottom (..)
    )

simplifyConditionsWithSmt
    ::  forall variable simplifier
    .   (MonadSimplify simplifier, InternalVariable variable)
    => SideCondition variable
    -> OrPattern variable
    -> simplifier (OrPattern variable)
simplifyConditionsWithSmt sideCondition unsimplified =
    OrPattern.gather $ do
        unsimplified1 <- BranchT.scatter unsimplified
        simplifyAndPrune unsimplified1
  where
    simplifyAndPrune
        :: Pattern variable -> BranchT simplifier (Pattern variable)
    simplifyAndPrune (Pattern.splitTerm -> (term, condition)) = do
        simplified <- simplifyCondition sideCondition condition
        filtered <-
            return simplified
            & resultWithFilter pruneCondition
            & resultWithFilter rejectCondition
            & lift
        return (term `Pattern.withCondition` filtered)

    resultWithFilter
        :: (Condition variable -> simplifier (Maybe Bool))
        -> simplifier (Condition variable)
        -> simplifier (Condition variable)
    resultWithFilter conditionFilter previousResult = do
        previous <- previousResult
        if isTop previous || isBottom previous
            then return previous
            else do
                filtered <- conditionFilter previous
                case filtered of
                    Just True ->
                        -- TODO(virgil): We should be able to return
                        -- Condition.top, but if 'a' is the only constructor
                        -- of a sort and 'v' is a variable, then the SMT
                        -- can detect that 'not v=a' is not satisfiable
                        -- so we may remove a substitution here. However,
                        -- we are not able to handle that properly.
                        return previous
                            { Conditional.predicate = makeTruePredicate_ }
                    Just False -> return Condition.bottom
                    Nothing -> return previous

    {- | Check if the side condition implies the argument. If so, then
    returns @Just True@. If the side condition never implies the argument,
    returns False. Otherwise, returns Nothing.

    Note that the SMT evaluators currently only allow us to detect the
    @Just True@ branch.

    The side condition implies the argument, i.e. @side → arg@, iff
    @¬side ∨ arg@ iff @not(side ∧ ¬arg)@.

    In other words:

    @side ∧ ¬arg@ is not satisfiable iff @side → arg@ is @⊤@.
    @side ∧ ¬arg@ is always true iff @side → arg@ is @⊥@
    -}
    pruneCondition :: Condition variable -> simplifier (Maybe Bool)
    pruneCondition condition = do
        implicationNegation <-
            OrCondition.gather
            $ simplifyCondition
                SideCondition.top
                (Condition.fromPredicate
                    (makeAndPredicate
                        sidePredicate
                        (makeNotPredicate $ Condition.toPredicate condition)
                    )
                )
        filteredConditions <- SMT.Evaluator.filterMultiOr implicationNegation
        if isTop filteredConditions
            then return (Just False)
            else if isBottom filteredConditions
                then return (Just True)
                else return Nothing

    rejectCondition :: Condition variable -> simplifier (Maybe Bool)
    rejectCondition condition = do
        simplifiedConditions <-
            OrCondition.gather
            $ simplifyCondition
                    SideCondition.top
                    (addPredicate condition)
        filteredConditions <- SMT.Evaluator.filterMultiOr simplifiedConditions
        if isBottom filteredConditions
            then return (Just False)
            else if isTop filteredConditions
                then return (Just True)
                else return Nothing


    sidePredicate = SideCondition.toPredicate sideCondition

    addPredicate :: Conditional variable term -> Conditional variable term
    addPredicate c@Conditional {predicate} =
        c {Conditional.predicate = makeAndPredicate predicate sidePredicate}
